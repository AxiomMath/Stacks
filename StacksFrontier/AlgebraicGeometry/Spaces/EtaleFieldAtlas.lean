module

public import Mathlib.RingTheory.Etale.Field
public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.AffineQuotient
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.GroupoidOfEquivalenceRelation
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.OverField
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Examples.OverField
public import StacksFrontier.AlgebraicGeometry.Size.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleQuotientPresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteEtaleAtlasQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.KernelPairRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafAlgebraic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Algebraic spaces with an étale atlas by the spectrum of a field

A quasi-separated algebraic space admitting a surjective étale morphism from the spectrum of a
field `k` is itself the spectrum of a field `k'`, and `k` is a finite separable extension of
`k'`.

## Main results

* `AlgebraicGeometry.Space.exists_iso_yoneda_of_isPullback`: an algebraic space with a
  surjective étale atlas is represented by any object of the site receiving from the atlas a
  faithfully flat morphism of finite presentation with the same kernel pair.
* `AlgebraicGeometry.Space.exists_quotient_of_isFiniteLocallyFree_relation`: a finite locally
  free equivalence relation on an affine scheme with affine scheme of arrows has an affine
  quotient, receiving a surjective finite locally free morphism whose kernel pair is the
  relation.
* `AlgebraicGeometry.Space.exists_algebra_isField_of_isFinite_flat_surjective`: a commutative
  ring whose spectrum receives a finite, flat and surjective morphism from the spectrum of a
  field is itself a field, and the field is a finite extension of it.
* `AlgebraicGeometry.Space.exists_iso_yoneda_spec_of_surjective_etale_fieldSpec`: a
  quasi-separated algebraic space admitting a surjective étale morphism from the spectrum of a
  field `k` is the spectrum of a field `k'`, and `k` is a finite separable extension of `k'`.

## References

* [Stacks Project, Tag 03BM](https://stacks.math.columbia.edu/tag/03BM)
* [Stacks Project, Tag 03DZ](https://stacks.math.columbia.edu/tag/03DZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.Space

/-- The comparison isomorphisms of `AlgebraicGeometry.Space.pointsYonedaIso` carry the map of
functors of points induced by a morphism between images of a fully faithful presenting functor
to the map of represented presheaves induced by its preimage. -/
theorem pointsYonedaIso_inv_comp {C : Type v} [Category.{u} C] {S : Scheme.{u}} (Φ : C ⥤ Over S)
    [Φ.Full] [Φ.Faithful] {X Y : C} (φ : Φ.obj X ⟶ Φ.obj Y) :
    (pointsYonedaIso Φ X).inv ≫ Φ.op.whiskerLeft (yoneda.map φ) ≫ (pointsYonedaIso Φ Y).hom =
      yoneda.map (Φ.preimage φ) := by
  ext V x
  refine Φ.map_injective ?_
  simp [pointsYonedaIso, Stacks.Groupoids.points, Functor.FullyFaithful.homEquiv,
    Functor.FullyFaithful.ofFullyFaithful]

/-- An algebraic space over `S` with a surjective étale atlas `f` whose kernel pair is
represented by `t, s : R ⟶ U` is represented by any object `U'` of the site receiving from `U`
a faithfully flat morphism of finite presentation whose kernel pair is again `t, s`. -/
theorem exists_iso_yoneda_of_isPullback
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    {U R U' : BigFppfOver B S hS} (f : yoneda.obj U ⟶ F) (t s : R ⟶ U)
    (hR : IsPullback (yoneda.map t) (yoneda.map s) f f)
    (hsurj : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) f)
    (hetale : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) f)
    (π : (Over.post B.inclusion).obj U ⟶ (Over.post B.inclusion).obj U')
    (hflat : Flat π.left) (hlfp : LocallyOfFinitePresentation π.left)
    (hsurjπ : Surjective π.left)
    (hπ : IsPullback ((Over.post B.inclusion).map t) ((Over.post B.inclusion).map s) π π) :
    ∃ (m : U ⟶ U') (e : F ≅ yoneda.obj U'),
      (Over.post B.inclusion).map m = π ∧ f ≫ e.hom = yoneda.map m := by
  classical
  obtain ⟨hRsh, hUsh, hcolimF⟩ :=
    isCoequalizer_of_surjectiveEtale B S hS f t s hR hF hsurj hetale
  set J := BigFppfOver.topology B S hS with hJ
  set RF : Sheaf J (Type u) := ⟨yoneda.obj R, hRsh⟩ with hRF
  set UF : Sheaf J (Type u) := ⟨yoneda.obj U, hUsh⟩ with hUF
  set FF : Sheaf J (Type u) := ⟨F, hF.isSheaf⟩ with hFF
  set MF : Sheaf J (Type u) :=
    ⟨Stacks.Groupoids.points (Over.post B.inclusion) ((Over.post B.inclusion).obj U'),
      Stacks.Groupoids.isSheaf_points B S hS ((Over.post B.inclusion).obj U')⟩ with hMF
  set tf : RF ⟶ UF := ⟨yoneda.map t⟩ with htf
  set sf : RF ⟶ UF := ⟨yoneda.map s⟩ with hsf
  set ff : UF ⟶ FF := ⟨f⟩ with hff
  set p : yoneda.obj U ⟶
      Stacks.Groupoids.points (Over.post B.inclusion) ((Over.post B.inclusion).obj U') :=
    (pointsYonedaIso (Over.post B.inclusion) U).inv ≫
      (Over.post B.inclusion).op.whiskerLeft (yoneda.map π) with hp
  have hpapp : ∀ (V : BigFppfOver B S hS) (g : V ⟶ U),
      p.app (op V) g = (Over.post B.inclusion).map g ≫ π := by
    intro V g
    simp [hp, pointsYonedaIso, Stacks.Groupoids.points,
      Functor.FullyFaithful.homEquiv, Functor.FullyFaithful.ofFullyFaithful]
  set pf : UF ⟶ MF := ⟨p⟩ with hpf
  have hwp : tf ≫ pf = sf ≫ pf := by
    apply Sheaf.hom_ext
    ext V g
    show p.app V ((yoneda.map t).app V g) = p.app V ((yoneda.map s).app V g)
    obtain ⟨V⟩ := V
    rw [show ((yoneda.map t).app (op V) g) = g ≫ t from rfl,
      show ((yoneda.map s).app (op V) g) = g ≫ s from rfl, hpapp, hpapp,
      Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, hπ.w]
  have hker : ∀ ⦃V : BigFppfOver B S hS⦄ (x y : UF.obj.obj (op V)),
      pf.hom.app (op V) x = pf.hom.app (op V) y →
      ∃ r : RF.obj.obj (op V), tf.hom.app (op V) r = x ∧ sf.hom.app (op V) r = y := by
    intro V x y hxy
    have hxy' : (Over.post B.inclusion).map x ≫ π = (Over.post B.inclusion).map y ≫ π :=
      (hpapp V x).symm.trans (hxy.trans (hpapp V y))
    refine ⟨(Over.post B.inclusion).preimage (hπ.lift _ _ hxy'), ?_, ?_⟩
    · show (Over.post B.inclusion).preimage (hπ.lift _ _ hxy') ≫ t = x
      refine (Over.post B.inclusion).map_injective ?_
      rw [Functor.map_comp, Functor.map_preimage]
      exact hπ.lift_fst _ _ hxy'
    · show (Over.post B.inclusion).preimage (hπ.lift _ _ hxy') ≫ s = y
      refine (Over.post B.inclusion).map_injective ?_
      rw [Functor.map_comp, Functor.map_preimage]
      exact hπ.lift_snd _ _ hxy'
  have h1 : Presheaf.IsLocallySurjective J
      ((Over.post B.inclusion).op.whiskerLeft (yoneda.map π)) :=
    isLocallySurjective_pointsMap_of_flat_locallyOfFinitePresentation_surjective B S hS π
  have hlocsurj : Presheaf.IsLocallySurjective J pf.hom := by
    show Presheaf.IsLocallySurjective J p
    rw [hp]
    infer_instance
  obtain ⟨hcolimM⟩ := Sheaf.nonempty_isColimitCoforkOfKernelPair tf sf pf hwp hker hlocsurj
  obtain ⟨hcolimF⟩ := hcolimF
  have hpres : f ≫ ((sheafToPresheaf J (Type u)).mapIso
      (IsColimit.coconePointUniqueUpToIso hcolimF hcolimM)).hom = p :=
    congrArg (fun h => h.hom)
      (IsColimit.comp_coconePointUniqueUpToIso_hom hcolimF hcolimM WalkingParallelPair.one)
  refine ⟨(Over.post B.inclusion).preimage π,
    (sheafToPresheaf J (Type u)).mapIso
      (IsColimit.coconePointUniqueUpToIso hcolimF hcolimM) ≪≫
        pointsYonedaIso (Over.post B.inclusion) U', Functor.map_preimage _ _, ?_⟩
  rw [Iso.trans_hom, ← Category.assoc, hpres, hp, Category.assoc, pointsYonedaIso_inv_comp]

/-- Being an internal equivalence relation is invariant under transporting the source and the
target of the pair along equalities of its two objects. -/
theorem isEquivalenceRelation_eqToHom_conj {C : Type*} [Category C] {R U R' U' : C}
    (hR : R' = R) (hU : U = U') (p₁ p₂ : R ⟶ U) [IsEquivalenceRelation p₁ p₂] :
    IsEquivalenceRelation (eqToHom hR ≫ p₁ ≫ eqToHom hU) (eqToHom hR ≫ p₂ ≫ eqToHom hU) := by
  subst hR
  subst hU
  simpa using ‹IsEquivalenceRelation p₁ p₂›

/-- A finite locally free equivalence relation on an affine scheme over `S` with affine scheme
of arrows admits a quotient: an affine scheme over `S`, no larger than the scheme it is a
quotient of, receiving a surjective finite locally free morphism whose kernel pair is the
relation. -/
@[sga "3 V 7.1" "special case"]
theorem exists_quotient_of_isFiniteLocallyFree_relation (S : Scheme.{u}) {R U : Over S}
    (t s : R ⟶ U) [IsAffine U.left] [IsAffine R.left]
    [Stacks.Morphisms.IsFiniteLocallyFree s.left]
    [Stacks.Morphisms.IsFiniteLocallyFree t.left]
    [IsEquivalenceRelation t s] :
    ∃ (A : Type u) (_ : CommRing A) (g : Spec (.of A) ⟶ S) (π : U ⟶ Over.mk g),
      (Spec (CommRingCat.of A)).size ≤ U.left.size ∧
        Stacks.Morphisms.IsFiniteLocallyFree π.left ∧ Surjective π.left ∧
        IsPullback t s π π := by
  classical
  set j : Stacks.Groupoids.PreRelation R U := prod.lift t s with hj
  have hjt : j.target = t := by simp [hj, Stacks.Groupoids.PreRelation.target]
  have hjs : j.source = s := by simp [hj, Stacks.Groupoids.PreRelation.source]
  have _ : IsEquivalenceRelation j.target j.source := by rw [hjt, hjs]; infer_instance
  obtain ⟨G, hGext, -⟩ := existsUnique_groupoidScheme_of_isEquivalenceRelation j
  obtain ⟨ho, ha, hsrc, htgt⟩ := hGext
  have hoL : G.objects.left = U.left := congrArg Over.left ho
  have haL : G.arrows.left = R.left := congrArg Over.left ha
  have hsrcG : G.source = eqToHom ha ≫ s ≫ eqToHom ho.symm := by
    rw [← hjs, ← hsrc]; simp
  have htgtG : G.target = eqToHom ha ≫ t ≫ eqToHom ho.symm := by
    rw [← hjt, ← htgt]; simp
  have hsrcL : G.source.left = eqToHom haL ≫ s.left ≫ eqToHom hoL.symm := by
    rw [hsrcG]; simp [Over.eqToHom_left]
  have htgtL : G.target.left = eqToHom haL ≫ t.left ≫ eqToHom hoL.symm := by
    rw [htgtG]; simp [Over.eqToHom_left]
  have _ : IsAffine G.objects.left := by rw [hoL]; infer_instance
  have _ : IsAffine G.arrows.left := by rw [haL]; infer_instance
  have hconj : ∀ (g : R ⟶ U) [Stacks.Morphisms.IsFiniteLocallyFree g.left],
      Stacks.Morphisms.IsFiniteLocallyFree (eqToHom haL ≫ g.left ≫ eqToHom hoL.symm) :=
    fun g _ ↦ MorphismProperty.RespectsIso.precomp
      (@Stacks.Morphisms.IsFiniteLocallyFree.{u}) _ _
      (MorphismProperty.RespectsIso.postcomp
        (@Stacks.Morphisms.IsFiniteLocallyFree.{u}) _ _ inferInstance)
  have _ : Stacks.Morphisms.IsFiniteLocallyFree G.source.left := by
    rw [hsrcL]
    exact hconj s
  have _ : Stacks.Morphisms.IsFiniteLocallyFree G.target.left := by
    rw [htgtL]
    exact hconj t
  have _ : IsEquivalenceRelation G.target G.source := by
    rw [hsrcG, htgtG]
    exact isEquivalenceRelation_eqToHom_conj ha ho.symm t s
  set π₀ : U ⟶ GroupoidScheme.invariantSpectrumOver G :=
    eqToHom ho.symm ≫ GroupoidScheme.toInvariantSpectrumOver G with hπ₀
  have hπL : π₀.left =
      eqToHom hoL.symm ≫ (GroupoidScheme.toInvariantSpectrumOver G).left := by
    rw [hπ₀]; simp [Over.eqToHom_left]
  have hsize : (Spec (CommRingCat.of ↥(invariantRing G))).size ≤ U.left.size := by
    rw [Scheme.size_Spec, Scheme.size_of_isAffine U.left]
    refine max_le_max le_rfl ?_
    calc Cardinal.mk ↥(CommRingCat.of ↥(invariantRing G))
        ≤ Cardinal.mk ↥Γ(G.objects.left, ⊤) :=
          Cardinal.mk_le_of_injective Subtype.val_injective
      _ = Cardinal.mk ↥Γ(U.left, ⊤) :=
          congrArg (fun X : Scheme.{u} => Cardinal.mk ↥Γ(X, ⊤)) hoL
  have hflf : Stacks.Morphisms.IsFiniteLocallyFree π₀.left := by
    rw [hπL]
    exact MorphismProperty.RespectsIso.precomp
      (@Stacks.Morphisms.IsFiniteLocallyFree.{u}) _ _
      (GroupoidScheme.isFiniteLocallyFree_objectsToInvariantSpectrum G)
  have _ : MorphismProperty.RespectsIso (@Surjective.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hsurj0 : Surjective (GroupoidScheme.toInvariantSpectrumOver G).left := by
    rw [GroupoidScheme.toInvariantSpectrumOver_left]
    exact ⟨GroupoidScheme.surjective_objectsToInvariantSpectrum G⟩
  have hsurjπ : Surjective π₀.left := by
    rw [hπL]
    exact MorphismProperty.RespectsIso.precomp (@Surjective.{u}) _ _ hsurj0
  have hpb : IsPullback t s π₀ π₀ := by
    refine (GroupoidScheme.isPullback_toInvariantSpectrumOver G).of_iso (eqToIso ha)
      (eqToIso ho) (eqToIso ho) (Iso.refl _) ?_ ?_ ?_ ?_
    · rw [htgtG]; simp
    · rw [hsrcG]; simp
    · rw [hπ₀]; simp
    · rw [hπ₀]; simp
  exact ⟨↥(invariantRing G), inferInstance,
    (GroupoidScheme.invariantSpectrumBaseMap G).val, π₀, hsize, hflf, hsurjπ, hpb⟩

/-! ### Rings under a field along a faithfully flat finite morphism -/

/-- A commutative ring whose spectrum receives a finite, flat and surjective morphism from the
spectrum of a field `k` is itself a field, and `k` is a finite extension of it. The given
morphism is then the one induced by that extension. -/
theorem exists_algebra_isField_of_isFinite_flat_surjective {A : Type u} [CommRing A]
    (k : Type u) [Field k] (ψ : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A))
    (hfin : _root_.AlgebraicGeometry.IsFinite ψ) (hflat : Flat ψ) (hsurj : Surjective ψ) :
    ∃ (_ : Algebra A k) (_ : Module.Finite A k), IsField A ∧
      ψ = Spec.map (CommRingCat.ofHom (algebraMap A k)) := by
  obtain ⟨φ, hφ⟩ := Spec.map_surjective ψ
  let instAlg : Algebra A k := φ.hom.toAlgebra
  have hφ' : φ = CommRingCat.ofHom (algebraMap A k) :=
    CommRingCat.hom_ext (RingHom.algebraMap_toAlgebra φ.hom).symm
  have hFin : _root_.AlgebraicGeometry.IsFinite (Spec.map φ) := by rw [hφ]; exact hfin
  let instFinite : Module.Finite A k :=
    (_root_.AlgebraicGeometry.IsFinite.SpecMap_iff φ).mp hFin
  let instFF : Module.FaithfullyFlat A k := by
    refine RingHom.faithfullyFlat_algebraMap_iff.mp ?_
    simpa [RingHom.algebraMap_toAlgebra] using
      (flat_and_surjective_SpecMap_iff φ).mp
        ⟨by rw [hφ]; exact hflat, by rw [hφ]; exact hsurj⟩
  have _ : Algebra.IsIntegral A k := Algebra.IsIntegral.of_finite A k
  refine ⟨instAlg, instFinite, isField_of_isIntegral_of_isField
    (FaithfulSMul.algebraMap_injective A k) (Field.toIsField k), ?_⟩
  rw [← hφ', hφ]

/-- A quasi-separated algebraic space over `S` admitting a surjective étale morphism from the
spectrum of a field `k` is the spectrum of a field `k'`, and `k` is a finite separable extension
of `k'`. -/
@[stacks 03DZ]
theorem exists_iso_yoneda_spec_of_surjective_etale_fieldSpec
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (hqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal F)
    (k : Type u) [Field k] {U : BigFppfOver B S hS}
    (eU : (BigFppfOver.toScheme B S hS).obj U ≅ Spec (.of k)) (f : yoneda.obj U ⟶ F)
    (hsurj : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) f)
    (hetale : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) f) :
    ∃ (k' : Type u) (_ : Field k') (_ : Algebra k' k) (_ : Module.Finite k' k)
      (_ : Algebra.IsSeparable k' k) (U' : BigFppfOver B S hS)
      (eU' : (BigFppfOver.toScheme B S hS).obj U' ≅ Spec (.of k'))
      (m : U ⟶ U') (e : F ≅ yoneda.obj U'),
      f ≫ e.hom = yoneda.map m ∧
        eU.inv ≫ (BigFppfOver.toScheme B S hS).map m ≫ eU'.hom =
          Spec.map (CommRingCat.ofHom (algebraMap k' k)) := by
  classical
  have hrep : yoneda.relativelyRepresentable f := hsurj.rep
  set R : BigFppfOver B S hS := hrep.pullback f with hRdef
  set t : R ⟶ U := hrep.fst' f with htdef
  set s : R ⟶ U := hrep.snd f with hsdef
  have hR : IsPullback (yoneda.map t) (yoneda.map s) f f := hrep.isPullback' f
  have hUcpt : CompactSpace ((BigFppfOver.toScheme B S hS).obj U) :=
    Stacks.Spaces.compactSpace_of_iso eU.symm inferInstance
  have hRcpt : CompactSpace ((BigFppfOver.toScheme B S hS).obj R) :=
    compactSpace_of_isAbsolutelyQuasiSeparated B S hS B.contains_terminal hqs hR hUcpt hUcpt
  have hUaff : IsAffine ((BigFppfOver.toScheme B S hS).obj U) := IsAffine.of_isIso eU.hom
  have _ : MorphismProperty.RespectsIso (@Etale.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hsE : Etale ((BigFppfOver.toScheme B S hS).map s) :=
    hetale.property f (yoneda.map t) s hR
  have htE : Etale ((BigFppfOver.toScheme B S hS).map t) :=
    hetale.property f (yoneda.map s) t hR.flip
  have hqE : ∀ g : R ⟶ U, Etale ((BigFppfOver.toScheme B S hS).map g) →
      Etale ((BigFppfOver.toScheme B S hS).map g ≫ eU.hom) := fun g hg ↦
    MorphismProperty.RespectsIso.postcomp (@Etale.{u}) eU.hom _ hg
  have hRaff : IsAffine ((BigFppfOver.toScheme B S hS).obj R) := by
    have _ : QuasiCompact ((BigFppfOver.toScheme B S hS).map s ≫ eU.hom) :=
      quasiCompact_of_compactSpace_of_isAffine _ inferInstance hRcpt
    obtain ⟨_, _⟩ := (etale_iff_unramified_over_field k
      ((BigFppfOver.toScheme B S hS).map s ≫ eU.hom)).mp (hqE s hsE)
    exact isAffine_of_unramified_quasiCompact k ((BigFppfOver.toScheme B S hS).map s ≫ eU.hom)
  have hflf : ∀ g : R ⟶ U, Etale ((BigFppfOver.toScheme B S hS).map g) →
      Stacks.Morphisms.IsFiniteLocallyFree ((BigFppfOver.toScheme B S hS).map g) := fun g hg ↦ by
    have _ := hqE g hg
    exact (MorphismProperty.cancel_right_of_respectsIso
      (@Stacks.Morphisms.IsFiniteLocallyFree.{u}) _ eU.hom).1
      ((Stacks.Morphisms.isFiniteLocallyFree_iff_of_specTarget _).mpr
        ⟨isFinite_of_isAffine_of_etale_over_field k _, inferInstance, inferInstance⟩)
  have _ : IsAffine ((Over.post B.inclusion).obj U).left := hUaff
  have _ : IsAffine ((Over.post B.inclusion).obj R).left := hRaff
  have _ : Stacks.Morphisms.IsFiniteLocallyFree ((Over.post B.inclusion).map s).left :=
    hflf s hsE
  have _ : Stacks.Morphisms.IsFiniteLocallyFree ((Over.post B.inclusion).map t).left :=
    hflf t htE
  have _ : IsEquivalenceRelation ((Over.post B.inclusion).map t)
      ((Over.post B.inclusion).map s) :=
    isEquivalenceRelation_of_isPullback B S hS f t s hR
  obtain ⟨A, _, g, π, hsize, hflf, hsurjπ, hpb⟩ :=
    exists_quotient_of_isFiniteLocallyFree_relation S
      ((Over.post B.inclusion).map t) ((Over.post B.inclusion).map s)
  have hk' : B.Contains (Spec (CommRingCat.of A)) := lt_of_le_of_lt hsize U.left.2
  set U' : BigFppfOver B S hS := Over.mk (⟨g⟩ : B.obj hk' ⟶ B.obj hS) with hU'def
  let eU' : (BigFppfOver.toScheme B S hS).obj U' ≅ Spec (CommRingCat.of A) := Iso.refl _
  obtain ⟨m, e, hmπ, he⟩ :=
    exists_iso_yoneda_of_isPullback B S hS hF f t s hR hsurj hetale (U' := U') π
      (Stacks.Morphisms.IsFiniteLocallyFree.flat π.left)
      (Stacks.Morphisms.IsFiniteLocallyFree.locallyOfFinitePresentation π.left) hsurjπ hpb
  have hmleft : (BigFppfOver.toScheme B S hS).map m = π.left :=
    congrArg (fun h => h.left) hmπ
  have hcancel : ∀ (P : MorphismProperty Scheme.{u}), P.RespectsIso →
      P π.left → P (eU.inv ≫ π.left) :=
    fun P _ hP ↦ MorphismProperty.RespectsIso.precomp P eU.inv _ hP
  obtain ⟨instAlg, instFinite, hAfield, hψ⟩ :=
    exists_algebra_isField_of_isFinite_flat_surjective (A := A) k (eU.inv ≫ π.left)
      (hcancel _ MorphismProperty.IsStableUnderBaseChange.respectsIso
        (Stacks.Morphisms.IsFiniteLocallyFree.isFinite π.left))
      (hcancel _ MorphismProperty.IsStableUnderBaseChange.respectsIso
        (Stacks.Morphisms.IsFiniteLocallyFree.flat π.left))
      (hcancel _ MorphismProperty.IsStableUnderBaseChange.respectsIso hsurjπ)
  let instFieldA : Field A := hAfield.toField
  have hPe : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)))
      (yoneda.map m) := by
    rw [← he]
    exact MorphismProperty.RespectsIso.postcomp _ e.hom f hetale
  have hmE : Etale ((BigFppfOver.toScheme B S hS).map m) :=
    MorphismProperty.of_relative_map
      (P := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)) (F := yoneda) hPe
  have hEt : Etale (Spec.map (CommRingCat.ofHom (algebraMap A k))) := by
    rw [← hψ]
    exact hcancel _ MorphismProperty.IsStableUnderBaseChange.respectsIso (hmleft ▸ hmE)
  have hSep : Algebra.IsSeparable A k := by
    have hre : RingHom.Etale (algebraMap A k) := by
      simpa using (HasRingHomProperty.Spec_iff (P := @Etale)).mp hEt
    have _ : Algebra.Etale A k := (RingHom.etale_algebraMap (R := A) (S := k)).mp hre
    rw [← Algebra.FormallyEtale.iff_isSeparable]
    infer_instance
  refine ⟨A, instFieldA, instAlg, instFinite, hSep, U', eU', m, e, he, ?_⟩
  rw [hmleft, ← hψ]
  exact congrArg (fun h => eU.inv ≫ h) (Category.comp_id π.left)

end AlgebraicGeometry.Space

end
