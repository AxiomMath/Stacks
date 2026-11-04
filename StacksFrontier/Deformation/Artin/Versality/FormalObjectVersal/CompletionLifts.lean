module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Algebraization
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteTypePoint
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.AlgebraicGeometry.Variety.CompleteLocal.Stalk
public import StacksFrontier.Deformation.Artin.FormalObject
public import StacksFrontier.Deformation.Artin.FormalObject.Predeformation
public import StacksFrontier.Deformation.Artin.FormalObject.Versal
public import StacksFrontier.Deformation.Artin.Predeformation
public import StacksFrontier.Deformation.Artin.Versality
public import StacksFrontier.Deformation.Artin.Versality.FormalObjectVersal.ApproximationLevels
public import StacksFrontier.Deformation.ArtinCriteria.Predeformation
public import StacksFrontier.Deformation.Basic
public import StacksFrontier.Deformation.Cofibered
public import StacksFrontier.Deformation.Completed.Basic
public import StacksFrontier.Deformation.FormalObject.Associated
public import StacksFrontier.Deformation.FormalObject.Basic
public import StacksFrontier.Deformation.Groupoid.BaseCategory
public import StacksFrontier.Deformation.Predeformation.Basic
public import StacksFrontier.Deformation.Smooth.Basic
public import StacksFrontier.Deformation.Smooth.Pushforward
public import StacksFrontier.Deformation.Smooth.Versal
public import StacksFrontier.RingTheory.Ideal.RadicalMaximalQuotient

/-!
# Artinian points through completed local rings and restriction cones

Auxiliary material for `Deformation.Artin.isVersalAt_iff_isVersal`: factorization through
strongly Cartesian arrows, local homomorphisms out of completed local rings and stalks and the
unique factorization of Artinian local points through a presentation of the completed local
ring, the forgetful functor of a predeformation category, the cone induced on the associated
morphism of a formal object by a compatible family of restrictions, smoothness read as
solvability of lifting triangles for such cones, and transport lemmas for underlying morphisms
of schemes.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

namespace Deformation.Artin

universe u v w

attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor
attribute [local implicit_reducible] CategoryTheory.Functor.Elements
attribute [local implicit_reducible] Deformation.Artin.baseOver
attribute [local implicit_reducible] Deformation.Artin.truncationOver

/-- A map to the base of a strongly Cartesian arrow lifts through that arrow. -/
private theorem factor_through_cartesian
    {C D : Type*} [Category C] [Category D]
    (p : C ⥤ D) {y z x : C} (r : z ⟶ x)
    (hr : p.IsStronglyCartesian (p.map r) r) (f : p.obj y ⟶ p.obj z)
    (g : y ⟶ x) (h : f ≫ p.map r = p.map g) :
    ∃ l : y ⟶ z, p.map l = f ∧ l ≫ r = g := by
  have : p.IsStronglyCartesian (p.map r) r := hr
  have hg : p.IsHomLift (f ≫ p.map r) g := by
    rw [h]
    infer_instance
  have : p.IsHomLift (f ≫ p.map r) g := hg
  let hf' : p.map g = f ≫ p.map r := h.symm
  let l := Functor.IsStronglyCartesian.map p (p.map r) r hf' g
  have hl : p.IsHomLift f l :=
    Functor.IsStronglyCartesian.map_isHomLift p (p.map r) r hf' g
  have : p.IsHomLift f l := hl
  exact ⟨l, (IsHomLift.eq_of_isHomLift p f l).symm,
    Functor.IsStronglyCartesian.fac p (p.map r) r hf' g⟩

/-- A lift through a strongly Cartesian arrow is unique. -/
theorem factor_through_cartesian_unique
    {C D : Type*} [Category C] [Category D]
    (p : C ⥤ D) {y z x : C} (r : z ⟶ x)
    (hr : p.IsStronglyCartesian (p.map r) r) {f : p.obj y ⟶ p.obj z}
    {g : y ⟶ x} (h : f ≫ p.map r = p.map g)
    (l₁ l₂ : y ⟶ z) (hl₁ : p.map l₁ = f) (hl₂ : p.map l₂ = f)
    (hc₁ : l₁ ≫ r = g) (hc₂ : l₂ ≫ r = g) : l₁ = l₂ := by
  have : p.IsStronglyCartesian (p.map r) r := hr
  have hf₁ : p.IsHomLift f l₁ := by
    have h : p.IsHomLift (p.map l₁) l₁ := inferInstance
    rw [hl₁] at h
    exact h
  have hf₂ : p.IsHomLift f l₂ := by
    have h : p.IsHomLift (p.map l₂) l₂ := inferInstance
    rw [hl₂] at h
    exact h
  have : p.IsHomLift f l₁ := hf₁
  have : p.IsHomLift f l₂ := hf₂
  calc
    l₁ = Functor.IsStronglyCartesian.map p (p.map r) r h.symm g :=
      Functor.IsStronglyCartesian.map_uniq p (p.map r) r h.symm g l₁ hc₁
    _ = l₂ := (Functor.IsStronglyCartesian.map_uniq p (p.map r) r h.symm g l₂ hc₂).symm


/-- A local homomorphism from a Noetherian local ring to an Artinian local ring factors
through the maximal-ideal-adic completion. -/
private theorem exists_localHom_completion
    {T A : Type*} [CommRing T] [IsNoetherianRing T] [IsLocalRing T]
    [CommRing A] [IsArtinianRing A] [IsLocalRing A]
    (f : T →+* A) [IsLocalHom f] :
    ∃ F : AdicCompletion (maximalIdeal T) T →+* A,
      IsLocalHom F ∧ F.comp (algebraMap T (AdicCompletion (maximalIdeal T) T)) = f := by
  obtain ⟨n, hn⟩ := (isArtinianRing_iff_isNilpotent_maximalIdeal A).mp inferInstance
  have hker : maximalIdeal T ^ n ≤ RingHom.ker f :=
    Ideal.pow_le_ker_of_map_le f (map_maximalIdeal_le f) hn
  let F := (Ideal.Quotient.lift (maximalIdeal T ^ n) f hker).comp
    (AdicCompletion.evalₐ (maximalIdeal T) n).toRingHom
  have hF : F.comp (algebraMap T (AdicCompletion (maximalIdeal T) T)) = f := by
    ext t
    simp only [RingHom.comp_apply, F]
    rfl
  refine ⟨F, ?_, hF⟩
  apply ((IsLocalRing.local_hom_TFAE F).out 1 3).mpr
  rw [AdicCompletion.maximalIdeal_eq_map,
    Ideal.map_map, hF]
  exact map_maximalIdeal_le f

/-- Two local homomorphisms out of the adic completion of a Noetherian local ring agree
as soon as they agree on the ring itself. -/
private theorem localHom_completion_ext
    {T A : Type*} [CommRing T] [IsNoetherianRing T] [IsLocalRing T]
    [CommRing A] [IsArtinianRing A] [IsLocalRing A]
    (f g : AdicCompletion (maximalIdeal T) T →+* A)
    [IsLocalHom f] [IsLocalHom g]
    (h : f.comp (algebraMap T (AdicCompletion (maximalIdeal T) T)) =
      g.comp (algebraMap T (AdicCompletion (maximalIdeal T) T))) : f = g := by
  obtain ⟨n, hn⟩ := (isArtinianRing_iff_isNilpotent_maximalIdeal A).mp inferInstance
  ext x
  obtain ⟨t, ht⟩ := Submodule.mkQ_surjective
    ((maximalIdeal T ^ n) • (⊤ : Submodule T T)) (x.val n)
  have hx : x - algebraMap T (AdicCompletion (maximalIdeal T) T) t ∈
      maximalIdeal (AdicCompletion (maximalIdeal T) T) ^ n := by
    rw [AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow,
      ← Submodule.restrictScalars_mem T, ← Ideal.smul_top_eq_map,
      AdicCompletion.pow_smul_top_eq_ker_eval (maximalIdeal T).fg_of_isNoetherianRing,
      LinearMap.mem_ker, map_sub]
    exact sub_eq_zero.mpr ht.symm
  have he (F : AdicCompletion (maximalIdeal T) T →+* A) [IsLocalHom F] :
      F x = F (algebraMap T (AdicCompletion (maximalIdeal T) T) t) := by
    have hm := Ideal.mem_map_of_mem F hx
    have hl := (Ideal.pow_right_mono (map_maximalIdeal_le F) n).trans_eq hn
    rw [← Ideal.map_pow] at hl
    simpa only [Submodule.zero_eq_bot, Ideal.mem_bot, map_sub, sub_eq_zero] using hl hm
  rw [he f, he g]
  exact DFunLike.congr_fun h t

/-- The underlying ring homomorphism of a ring isomorphism is a local homomorphism. -/
private instance isLocalHom_toRingHom_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) : IsLocalHom e.toRingHom where
  map_nonunit _ h := (isLocalHom_equiv e).map_nonunit _ h

/-- A morphism from the spectrum of a local ring whose closed point maps to `x` factors
through the local ring of `X` at `x`. -/
public theorem exists_localHom_fromSpecStalk
    (X : Scheme.{u}) (x : X) {A : Type u} [CommRing A] [IsLocalRing A]
    (f : Spec (.of A) ⟶ X) (hf : f (closedPoint A) = x) :
    ∃ φ : X.presheaf.stalk x →+* A,
      IsLocalHom φ ∧ Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk x = f := by
  obtain ⟨⟨y, φ, hφ⟩, h⟩ := (SpecToEquivOfLocalRing X (.of A)).symm.surjective f
  change Spec.map φ ≫ X.fromSpecStalk y = f at h
  have hy : y = x := by
    have : IsLocalHom φ.hom := hφ
    have hc : (Spec.map φ ≫ X.fromSpecStalk y) (closedPoint A) = y :=
      (closedPoint_comp_eq φ (X.fromSpecStalk y)).trans Scheme.fromSpecStalk_closedPoint
    rw [← hf, ← h]
    exact hc.symm
  subst y
  exact ⟨φ.hom, hφ, h⟩

/-- A local homomorphism out of a stalk is determined by the morphism of spectra it
induces over `X`. -/
public theorem localHom_fromSpecStalk_injective
    (X : Scheme.{u}) (x : X) {A : Type u} [CommRing A] [IsLocalRing A]
    (f g : X.presheaf.stalk x →+* A) [IsLocalHom f] [IsLocalHom g]
    (h : Spec.map (CommRingCat.ofHom f) ≫ X.fromSpecStalk x =
      Spec.map (CommRingCat.ofHom g) ≫ X.fromSpecStalk x) : f = g := by
  have he : (⟨x, CommRingCat.ofHom f, inferInstance⟩ :
      Σ y, { f : X.presheaf.stalk y ⟶ CommRingCat.of A // IsLocalHom f.hom }) =
      ⟨x, CommRingCat.ofHom g, inferInstance⟩ :=
    (SpecToEquivOfLocalRing X (.of A)).symm.injective h
  have he' := (SpecToEquivOfLocalRing_eq_iff.mp he).choose_spec
  rw [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl,
    Category.id_comp] at he'
  exact congrArg CommRingCat.Hom.hom he'

/-- An Artinian local point of a locally Noetherian scheme factors uniquely, and locally,
through the completed local ring at its image. -/
private theorem exists_unique_completedLocalRing_lift
    (X : Scheme.{u}) [IsLocallyNoetherian X] (x : X)
    {A : Type u} [CommRing A] [IsArtinianRing A] [IsLocalRing A]
    (f : Spec (.of A) ⟶ X) (hf : f (closedPoint A) = x) :
    ∃! φ : { φ : AlgebraicGeometry.Scheme.completedLocalRing X x →+* A // IsLocalHom φ },
      Spec.map (CommRingCat.ofHom φ.1) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x)
          (AlgebraicGeometry.Scheme.completedLocalRing X x))) ≫ X.fromSpecStalk x = f := by
  obtain ⟨φ, hφ, he⟩ := exists_localHom_fromSpecStalk X x f hf
  have : IsLocalHom φ := hφ
  obtain ⟨ψ, hψ, heψ⟩ := exists_localHom_completion φ
  refine ⟨⟨ψ, hψ⟩, ?_, ?_⟩
  · dsimp only
    rw [← Spec.map_comp_assoc]
    show Spec.map (CommRingCat.ofHom (ψ.comp (algebraMap _ _))) ≫ _ = _
    rw [heψ, he]
  · rintro ⟨ψ', hψ'⟩ heψ'
    apply Subtype.ext
    have : IsLocalHom ψ := hψ
    have : IsLocalHom ψ' := hψ'
    apply localHom_completion_ext
    apply localHom_fromSpecStalk_injective X x
    show Spec.map (CommRingCat.ofHom (ψ'.comp (algebraMap _ _))) ≫ _ =
      Spec.map (CommRingCat.ofHom (ψ.comp (algebraMap _ _))) ≫ _
    rw [heψ, he]
    rw [← Spec.map_comp_assoc] at heψ'
    convert heψ' using 1
    congr 2

/-- The canonical morphism out of a presentation of the completed local ring sends the
closed point to `x`. -/
public theorem completionPresentation_closedPoint
    (X : Scheme.{u}) [IsLocallyNoetherian X] (x : X)
    {R : Type u} [CommRing R] [IsLocalRing R]
    (e : AlgebraicGeometry.Scheme.completedLocalRing X x ≃+* R) :
    (Spec.map (CommRingCat.ofHom e.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x)
        (AlgebraicGeometry.Scheme.completedLocalRing X x))) ≫ X.fromSpecStalk x)
        (closedPoint R) = x := by
  have : IsLocalHom (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x)
      (AlgebraicGeometry.Scheme.completedLocalRing X x))).hom :=
    inferInstanceAs (IsLocalHom (algebraMap (X.presheaf.stalk x)
      (AlgebraicGeometry.Scheme.completedLocalRing X x)))
  have : IsLocalHom (CommRingCat.ofHom e.toRingHom).hom :=
    inferInstanceAs (IsLocalHom e.toRingHom)
  exact (closedPoint_comp_eq (CommRingCat.ofHom e.toRingHom) _).trans
    ((closedPoint_comp_eq (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x)
        (AlgebraicGeometry.Scheme.completedLocalRing X x))) (X.fromSpecStalk x)).trans
      Scheme.fromSpecStalk_closedPoint)

/-- The unique factorization of an Artinian local point, transported along a presentation
of the completed local ring. -/
public theorem exists_unique_completionPresentation_lift
    (X : Scheme.{u}) [IsLocallyNoetherian X] (x : X)
    {R : Type u} [CommRing R] [IsLocalRing R]
    (e : AlgebraicGeometry.Scheme.completedLocalRing X x ≃+* R)
    {A : Type u} [CommRing A] [IsArtinianRing A] [IsLocalRing A]
    (f : Spec (.of A) ⟶ X) (hf : f (closedPoint A) = x) :
    ∃! φ : { φ : R →+* A // IsLocalHom φ },
      Spec.map (CommRingCat.ofHom φ.1) ≫
        Spec.map (CommRingCat.ofHom e.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x)
          (AlgebraicGeometry.Scheme.completedLocalRing X x))) ≫ X.fromSpecStalk x = f := by
  obtain ⟨φ, hφ, huniq⟩ := exists_unique_completedLocalRing_lift X x f hf
  have := φ.2
  refine ⟨⟨φ.1.comp e.symm.toRingHom, inferInstance⟩, ?_, ?_⟩
  · dsimp only
    have hcomp : (φ.1.comp e.symm.toRingHom).comp e.toRingHom = φ.1 := by
      ext t
      simp
    simpa only [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp,
      ← RingHom.comp_assoc, hcomp] using hφ
  · rintro ⟨ψ, hψ⟩ hψf
    have := hψ
    have hψφ : ψ.comp e.toRingHom = φ.1 := by
      have he := huniq ⟨ψ.comp e.toRingHom, inferInstance⟩ (by
        simpa only [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, RingHom.comp_assoc] using hψf)
      exact congrArg Subtype.val he
    apply Subtype.ext
    ext t
    have he := DFunLike.congr_fun hψφ (e.symm t)
    simpa using he

/-- Two local maps out of a presentation of the completed local ring which induce the same
morphism of spectra over `X` are equal. -/
public theorem completionPresentation_map_injective
    (X : Scheme.{u}) [IsLocallyNoetherian X] (x : X)
    {R : Type u} [CommRing R] [IsLocalRing R]
    (e : AlgebraicGeometry.Scheme.completedLocalRing X x ≃+* R)
    {A : Type u} [CommRing A] [IsArtinianRing A] [IsLocalRing A]
    (φ ψ : R →+* A) [IsLocalHom φ] [IsLocalHom ψ]
    (h : Spec.map (CommRingCat.ofHom φ) ≫
        Spec.map (CommRingCat.ofHom e.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x)
          (AlgebraicGeometry.Scheme.completedLocalRing X x))) ≫ X.fromSpecStalk x =
      Spec.map (CommRingCat.ofHom ψ) ≫
        Spec.map (CommRingCat.ofHom e.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x)
          (AlgebraicGeometry.Scheme.completedLocalRing X x))) ≫ X.fromSpecStalk x) : φ = ψ := by
  have he : φ.comp e.toRingHom = ψ.comp e.toRingHom := by
    apply localHom_completion_ext
    apply localHom_fromSpecStalk_injective X x
    simpa only [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, RingHom.comp_assoc] using h
  ext r
  simpa using DFunLike.congr_fun he (e.symm r)

/-- The identification of the residue field of `X` at `x` with the residue field of a
presentation of the completed local ring there. -/
public def completionResidueEquiv
    (X : Scheme.{u}) [IsLocallyNoetherian X] (x : X)
    {R : Type u} [CommRing R] [IsLocalRing R]
    (e : AlgebraicGeometry.Scheme.completedLocalRing X x ≃+* R) :
    X.residueField x ≃+* ResidueField R :=
  (RingEquiv.ofBijective
    (ResidueField.map (algebraMap (X.presheaf.stalk x)
      (AlgebraicGeometry.Scheme.completedLocalRing X x)))
    (AlgebraicGeometry.Scheme.completedLocalRing_residueFieldMap_bijective X x)).trans
    (ResidueField.mapEquiv e)
/-- The residue-field identification is compatible with the canonical morphisms to `X`. -/
public theorem completionResidueEquiv_spec
    (X : Scheme.{u}) [IsLocallyNoetherian X] (x : X)
    {R : Type u} [CommRing R] [IsLocalRing R]
    (e : AlgebraicGeometry.Scheme.completedLocalRing X x ≃+* R) :
    Spec.map (CommRingCat.ofHom (completionResidueEquiv X x e).toRingHom) ≫
        X.fromSpecResidueField x =
      Spec.map (CommRingCat.ofHom (residue R)) ≫
        Spec.map (CommRingCat.ofHom e.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x)
          (AlgebraicGeometry.Scheme.completedLocalRing X x))) ≫ X.fromSpecStalk x := by
  unfold Scheme.fromSpecResidueField
  simp only [← Spec.map_comp_assoc]
  congr 1

/-- An Artinian point of `U` compatible with the base and with the residue field factors
uniquely through the complete local presentation, as a morphism of `𝒞-hat_Λ`. -/
public theorem exists_completeLocalAlgHom_of_completionPresentation
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {S : Scheme.{u}} (iΛ : Spec (.of Λ) ⟶ S) [Mono iΛ]
    (U : Over S) [IsLocallyNoetherian U.left] (x : U.left)
    (R : Deformation.CompleteLocalAlgCat.{u, u, u} Λ k)
    (e : AlgebraicGeometry.Scheme.completedLocalRing U.left x ≃+* R)
    (g : Spec (.of R) ⟶ U.left)
    (hg : g = Spec.map (CommRingCat.ofHom e.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (U.left.presheaf.stalk x)
        (AlgebraicGeometry.Scheme.completedLocalRing U.left x))) ≫ U.left.fromSpecStalk x)
    (hbase : Spec.map (CommRingCat.ofHom (algebraMap Λ R)) ≫ iΛ = g ≫ U.hom)
    (A : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k)
    (f : Spec (.of A) ⟶ U.left) (hf : f (closedPoint A) = x)
    (hfbase : f ≫ U.hom = Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ)
    (hfres : Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap A)) ≫ f =
      Spec.map (CommRingCat.ofHom (R.residueEquiv.toAlgHom.toRingHom.comp
        (residue R))) ≫ g) :
    ∃! α : R ⟶ Deformation.artinianToComplete.obj A,
      Spec.map (CommRingCat.ofHom α.hom.toRingHom) ≫ g = f := by
  obtain ⟨⟨α, hα⟩, hαf, huniq⟩ := exists_unique_completionPresentation_lift U.left x e f hf
  have : IsLocalHom α := hα
  have hαf' : Spec.map (CommRingCat.ofHom α) ≫ g = f := by
    simpa only [hg] using hαf
  have hαalg : α.comp (algebraMap Λ R) = algebraMap Λ A := by
    have he : Spec.map (CommRingCat.ofHom (α.comp (algebraMap Λ R))) ≫ iΛ =
        Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ := by
      rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, hbase,
        ← Category.assoc, hαf', hfbase]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono iΛ).mp he))
  let ρ : R →+* k := R.residueEquiv.toAlgHom.toRingHom.comp (residue R)
  have : IsLocalHom (Deformation.Artin.residueMap A) := IsLocalHom.of_surjective _
    (A.residueEquiv.surjective.comp (residue_surjective (R := A)))
  have : IsLocalHom ρ := IsLocalHom.of_surjective _
    (R.residueEquiv.surjective.comp (residue_surjective (R := R)))
  have hαres : (Deformation.Artin.residueMap A).comp α = ρ := by
    apply completionPresentation_map_injective U.left x e
    rw [← hg, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, hαf']
    exact hfres
  let a : R ⟶ Deformation.artinianToComplete.obj A := {
    hom := { __ := α, commutes' := DFunLike.congr_fun hαalg }
    isLocal := hα
    residue_comm := DFunLike.congr_fun hαres
  }
  refine ⟨a, hαf', ?_⟩
  intro b hb
  have he : b.hom.toRingHom = α := by
    have : IsLocalHom b.hom.toRingHom := b.isLocal
    exact congrArg Subtype.val (huniq ⟨b.hom.toRingHom, b.isLocal⟩
      (by simpa only [← hg] using hb))
  exact Deformation.CompleteLocalAlgCat.Hom.ext (AlgHom.coe_ringHom_injective he)

/-- The functor from the opposite of a predeformation category to the ambient category,
sending a deformation to its underlying object and a morphism to its reversed arrow. -/
@[implicit_reducible]
public def deformationForget
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {S : Scheme.{u}} {iΛ : Spec (.of Λ) ⟶ S}
    {F : Type v} [Category.{w} F] {q : F ⥤ Over S}
    {x₀ : F} {hx₀ : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}
    (C : Deformation.Artin.PredeformationConstruction iΛ q x₀ hx₀) : C.carrierᵒᵖ ⥤ F where
  obj a := (C.objects a.unop).point
  map f := (C.morphisms _ _ f.unop).arrow
  map_id a := C.reversed_identity a.unop
  map_comp f g := C.reversed_composition g.unop f.unop

/-- A compatible family of maps out of the levels of a formal object is compatible with
the composite transition maps. -/
private theorem transitionTo_restriction
    {Λ : Type u} {k : Type v} [CommRing Λ] [Field k] [Algebra Λ k]
    {C : Type*} [Category C]
    {p : C ⥤ Deformation.ArtinianLocalAlgCat.{u, w, v} Λ k}
    (η : Deformation.FormalObject p) {F : Type*} [Category F]
    (G : Cᵒᵖ ⥤ F) {x : F} (r : ∀ n, G.obj (.op (η.level n)) ⟶ x)
    (hr : ∀ n, G.map (η.transition n).op ≫ r (n + 1) = r n)
    {n m : ℕ} (hnm : n ≤ m) :
    G.map (Deformation.transitionTo η hnm).op ≫
      r m = r n := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm
  unfold Deformation.transitionTo
  generalize_proofs h
  revert h
  rw [Nat.add_sub_cancel_left]
  intro h
  simp only [eqToHom_refl, Category.id_comp]
  induction d with
  | zero => simp [Deformation.transitionIter]
  | succ d ih =>
    simp only [Deformation.transitionIter,
      op_comp, Functor.map_comp, Category.assoc]
    have hstep : G.map (η.transition (n + d)).op ≫ r (n + (d + 1)) = r (n + d) := hr (n + d)
    rw [hstep]
    exact ih (Nat.le_add_right _ _) rfl

/-- The cone on the associated morphism of a formal object induced by a compatible family
of maps out of its levels. -/
public def associatedMorphismRestriction
    {Λ : Type u} {k : Type v} [CommRing Λ] [Field k] [Algebra Λ k]
    {C : Type*} [Category C]
    {p : C ⥤ Deformation.ArtinianLocalAlgCat.{u, w, v} Λ k}
    (η : Deformation.FormalObject p)
    {P : Deformation.ChosenPushforwards p}
    (H : Deformation.AssociatedMorphism η P)
    {F : Type*} [Category F] (G : Cᵒᵖ ⥤ F) {x : F}
    (r : ∀ n, G.obj (.op (η.level n)) ⟶ x)
    (hr : ∀ n, G.map (η.transition n).op ≫ r (n + 1) = r n) :
    H.toBasedFunctor.toFunctor.op ⋙ G ⟶ (Functor.const _).obj x where
  app α := G.map (H.pointInclusion α.unop).op ≫ r (H.level α.unop)
  naturality α β f := by
    change G.map (H.toBasedFunctor.map f.unop).op ≫
        (G.map (H.pointInclusion β.unop).op ≫ r (H.level β.unop)) =
      (G.map (H.pointInclusion α.unop).op ≫ r (H.level α.unop)) ≫ 𝟙 x
    rw [Category.comp_id]
    have h := congrArg (fun a => G.map a.op)
      (H.map_pointInclusion f.unop)
    simp only [op_comp, Functor.map_comp] at h
    have h' := congrArg (fun a => a ≫ r (max (H.level β.unop) (H.level α.unop))) h
    simp only [Category.assoc, transitionTo_restriction η G r hr] at h'
    simpa only [Category.assoc] using h'

/-- Smoothness of a morphism of based categories solves every lifting problem for a cone
on it. -/
theorem smooth_lifts_restriction_triangle
    {Λ : Type u} {k : Type v} [CommRing Λ] [Field k] [Algebra Λ k]
    {C D : Type*} [Category C] [Category D]
    {pC : C ⥤ Deformation.ArtinianLocalAlgCat.{u, w, v} Λ k}
    {pD : D ⥤ Deformation.ArtinianLocalAlgCat.{u, w, v} Λ k}
    (H : BasedFunctor (BasedCategory.ofFunctor pC) (BasedCategory.ofFunctor pD))
    (hH : Deformation.IsSmooth H)
    {F : Type*} [Category F] (G : Dᵒᵖ ⥤ F) {x : F}
    (r : H.toFunctor.op ⋙ G ⟶ (Functor.const _).obj x)
    {A B : Deformation.ArtinianLocalAlgCat.{u, w, v} Λ k}
    (f : B ⟶ A) (hf : Function.Surjective f.hom)
    (y : D) (α : C) (i : y ⟶ H.obj α) (hi : pD.IsHomLift f i) :
    ∃ b : G.obj (.op y) ⟶ x, G.map i.op ≫ b = r.app (.op α) := by
  obtain ⟨β, j, a, hj, ha, he⟩ := hH f hf y α i hi
  refine ⟨G.map a.op ≫ r.app (.op β), ?_⟩
  have he' := congrArg (fun i => G.map i.op) he
  simp only [op_comp, Functor.map_comp] at he'
  have hn := r.naturality j.op
  change G.map (H.map j).op ≫ r.app (.op β) = r.app (.op α) ≫ 𝟙 x at hn
  rw [he'] at hn
  exact (Category.assoc _ _ _).symm.trans (hn.trans (Category.comp_id _))

/-- Conversely a morphism of based categories is smooth once every lifting problem for a
cone on it is solvable and the cone detects objects and morphisms. -/
theorem isSmooth_of_lifts_restriction_triangles
    {Λ : Type u} {k : Type v} [CommRing Λ] [Field k] [Algebra Λ k]
    {C D : Type*} [Category C] [Category D]
    {pC : C ⥤ Deformation.ArtinianLocalAlgCat.{u, w, v} Λ k}
    {pD : D ⥤ Deformation.ArtinianLocalAlgCat.{u, w, v} Λ k}
    (H : BasedFunctor (BasedCategory.ofFunctor pC) (BasedCategory.ofFunctor pD))
    {F : Type*} [Category F] (G : Dᵒᵖ ⥤ F) {x : F}
    (r : H.toFunctor.op ⋙ G ⟶ (Functor.const _).obj x)
    (Q : ∀ y : D, (G.obj (.op y) ⟶ x) → Prop)
    (hobj : ∀ y b, Q y b → ∃ (β : C) (a : H.obj β ⟶ y),
      pD.IsHomLift (𝟙 (pD.obj y)) a ∧ G.map a.op ≫ r.app (.op β) = b)
    (hfull : ∀ {α β : C} (j : H.obj β ⟶ H.obj α),
      G.map j.op ≫ r.app (.op β) = r.app (.op α) →
        ∃ h : β ⟶ α, H.map h = j)
    (hlift : ∀ {A B : Deformation.ArtinianLocalAlgCat.{u, w, v} Λ k}
      (f : B ⟶ A), Function.Surjective f.hom →
        ∀ (y : D) (α : C) (i : y ⟶ H.obj α), pD.IsHomLift f i →
          ∃ b : G.obj (.op y) ⟶ x, Q y b ∧ G.map i.op ≫ b = r.app (.op α)) :
    Deformation.IsSmooth H := by
  intro B A f hf y α i hi
  obtain ⟨b, hb, hbi⟩ := hlift f hf y α i hi
  obtain ⟨β, a, ha, hab⟩ := hobj y b hb
  have ht : G.map (a ≫ i).op ≫ r.app (.op β) = r.app (.op α) := by
    simpa only [op_comp, Functor.map_comp, Category.assoc, hab] using hbi
  obtain ⟨h, hh⟩ := hfull (a ≫ i) ht
  have : pD.IsHomLift f i := hi
  have hB := IsHomLift.domain_eq pD f i
  have ha' : pD.IsHomLift (𝟙 B) a := hB ▸ ha
  have := ha'
  have hh' : pD.IsHomLift f (H.map h) := by
    rw [hh]
    simpa only [Category.id_comp] using (IsHomLift.comp pD (𝟙 B) f a i)
  exact ⟨β, h, a, (H.isHomLift_iff f h).mp hh', ha', hh⟩

/-- Compatibility of a family of maps transported along levelwise identifications of the
objects and heterogeneous identifications of the transition maps. -/
public theorem restriction_compatible_of_heq
    {C F : Type*} [Category C] [Category F]
    (G : Cᵒᵖ ⥤ F) (a : ℕ → C) (b : ℕ → F)
    (t : ∀ n, a (n + 1) ⟶ a n) (s : ∀ n, b n ⟶ b (n + 1))
    (e : ∀ n, G.obj (.op (a n)) = b n)
    (ht : ∀ n, HEq (G.map (t n).op) (s n))
    {x : F} (r : ∀ n, b n ⟶ x) (hr : ∀ n, s n ≫ r (n + 1) = r n)
    (n : ℕ) :
    G.map (t n).op ≫ (eqToHom (e (n + 1)) ≫ r (n + 1)) = eqToHom (e n) ≫ r n := by
  have hs : G.map (t n).op ≫ eqToHom (e (n + 1)) = eqToHom (e n) ≫ s n := by
    have h := (conj_eqToHom_iff_heq _ _ (e n) (e (n + 1))).mpr (ht n)
    simpa only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id] using
      congrArg (fun f => f ≫ eqToHom (e (n + 1))) h
  rw [← Category.assoc, hs, Category.assoc, hr]

/-- Two morphisms of deformations with the same reversed arrow are equal. -/
theorem deformationMorphism_ext
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {S : Scheme.{u}} {iΛ : Spec (.of Λ) ⟶ S}
    {F : Type v} [Category.{w} F] {q : F ⥤ Over S}
    {x₀ : F} {hx₀ : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}
    {a b : Deformation.Artin.DeformationObject iΛ q x₀ hx₀}
    {f g : Deformation.Artin.DeformationMorphism iΛ q x₀ hx₀ a b}
    (h : f.arrow = g.arrow) : f = g := by
  have hbase : f.ringHom = g.ringHom := by
    apply Deformation.ArtinianLocalAlgCat.hom_ext
    apply AlgHom.coe_ringHom_injective
    have hspec : Spec.map (CommRingCat.ofHom f.ringHom.hom.toRingHom) =
        Spec.map (CommRingCat.ofHom g.ringHom.hom.toRingHom) := by
      rw [← f.arrow_base, ← g.arrow_base, h]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective hspec)
  cases f
  cases g
  cases h
  cases hbase
  rfl

/-- The forgetful functor of a predeformation category is faithful. -/
public theorem deformationForget_faithful
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {S : Scheme.{u}} {iΛ : Spec (.of Λ) ⟶ S}
    {F : Type v} [Category.{w} F] {q : F ⥤ Over S}
    {x₀ : F} {hx₀ : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}
    (C : Deformation.Artin.PredeformationConstruction iΛ q x₀ hx₀) :
    (deformationForget C).Faithful where
  map_injective h := Quiver.Hom.unop_inj ((C.morphisms _ _).injective (deformationMorphism_ext h))

/-- Unique factorization through a strongly Cartesian arrow, with the base map given after
a fully faithful functor. -/
theorem factor_through_cartesian_comp_fullyFaithful
    {C D E : Type*} [Category C] [Category D] [Category E]
    (p : C ⥤ D) (J : D ⥤ E) [J.Full] [J.Faithful]
    {y z x : C} (r : z ⟶ x) (hr : p.IsStronglyCartesian (p.map r) r)
    (f : (p ⋙ J).obj y ⟶ (p ⋙ J).obj z) (g : y ⟶ x)
    (h : f ≫ (p ⋙ J).map r = (p ⋙ J).map g) :
    ∃! l : y ⟶ z, (p ⋙ J).map l = f ∧ l ≫ r = g := by
  have hf : J.preimage f ≫ p.map r = p.map g := by
    apply J.map_injective
    simpa only [Functor.comp_map, Functor.map_comp, Functor.map_preimage] using h
  obtain ⟨l, hl, hc⟩ := factor_through_cartesian p r hr (J.preimage f) g hf
  refine ⟨l, ⟨?_, hc⟩, ?_⟩
  · show J.map (p.map l) = f
    rw [hl, J.map_preimage]
  · intro l' hl'
    apply factor_through_cartesian_unique p r hr hf l' l _ hl hl'.2 hc
    apply J.map_injective
    simpa only [Functor.comp_map, Functor.map_preimage] using hl'.1

/-- The morphism of schemes underlying a morphism of the ambient category, read through
identifications of its source and target with prescribed objects over `S`. -/
public abbrev schemeMap
    {S : Scheme.{u}} {F : Type v} [Category.{w} F]
    (q : F ⥤ Over S) {y z : F} {Y Z : Over S}
    (hy : q.obj y = Y) (hz : q.obj z = Z) (f : y ⟶ z) : Y.left ⟶ Z.left :=
  eqToHom (congrArg Over.left hy).symm ≫ (q.map f).left ≫
    eqToHom (congrArg Over.left hz)

/-- The underlying morphism of schemes is compatible with composition. -/
public theorem schemeMap_comp
    {S : Scheme.{u}} {F : Type v} [Category.{w} F]
    (q : F ⥤ Over S) {y z x : F} {Y Z X : Over S}
    (hy : q.obj y = Y) (hz : q.obj z = Z) (hx : q.obj x = X)
    (f : y ⟶ z) (g : z ⟶ x) :
    schemeMap q hy hx (f ≫ g) = schemeMap q hy hz f ≫ schemeMap q hz hx g := by
  simp [schemeMap, Functor.map_comp, Category.assoc]

/-- Precomposing with a transport gives a transport on underlying morphisms of schemes. -/
public theorem schemeMap_eqToHom_comp
    {S : Scheme.{u}} {F : Type v} [Category.{w} F]
    (q : F ⥤ Over S) {y y' z : F} {Y Y' Z : Over S}
    (hy : q.obj y = Y) (hy' : q.obj y' = Y') (hz : q.obj z = Z)
    (e : y = y') (eY : Y.left = Y'.left) (f : y' ⟶ z) :
    schemeMap q hy hz (eqToHom e ≫ f) = eqToHom eY ≫ schemeMap q hy' hz f := by
  subst y' Y Y'
  simp [schemeMap]

/-- The spectrum of a quotient map is unchanged by transport along an equality of ideals. -/
public theorem quotientSpecMap_eqToHom
    (R : Type u) [CommRing R] {I J : Ideal R} (hIJ : I = J)
    (h : Spec (.of (R ⧸ J)) = Spec (.of (R ⧸ I))) :
    eqToHom h ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) := by
  cases hIJ
  simp

/-- Injectivity of the Artinian points of a complete local algebra transports along an
equality of complete local algebras. -/
public theorem completeLocalAlg_points_injective_of_eq
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {R T : Deformation.CompleteLocalAlgCat.{u, u, u} Λ k}
    (h : R = T) {X : Scheme.{u}} (g : Spec (.of T) ⟶ X)
    (hinj : ∀ (A : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k)
      (α β : T ⟶ Deformation.artinianToComplete.obj A),
      Spec.map (CommRingCat.ofHom α.hom.toRingHom) ≫ g =
        Spec.map (CommRingCat.ofHom β.hom.toRingHom) ≫ g → α = β)
    (A : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k)
    (α β : R ⟶ Deformation.artinianToComplete.obj A)
    (he : Spec.map (CommRingCat.ofHom α.hom.toRingHom) ≫
        eqToHom (congrArg (fun R : Deformation.CompleteLocalAlgCat.{u, u, u} Λ k =>
          Spec (.of R)) h) ≫ g =
      Spec.map (CommRingCat.ofHom β.hom.toRingHom) ≫
        eqToHom (congrArg (fun R : Deformation.CompleteLocalAlgCat.{u, u, u} Λ k =>
          Spec (.of R)) h) ≫ g) : α = β := by
  subst T
  exact hinj A α β (by simpa using he)

/-- Existence of Artinian points of a complete local algebra transports along an equality
of complete local algebras. -/
public theorem completeLocalAlg_points_of_eq
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {R T : Deformation.CompleteLocalAlgCat.{u, u, u} Λ k}
    (h : R = T) {X : Scheme.{u}} (g : Spec (.of T) ⟶ X)
    (A : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k)
    (f : Spec (.of A) ⟶ X)
    (hf : ∃ α : T ⟶ Deformation.artinianToComplete.obj A,
      Spec.map (CommRingCat.ofHom α.hom.toRingHom) ≫ g = f) :
    ∃ α : R ⟶ Deformation.artinianToComplete.obj A,
      Spec.map (CommRingCat.ofHom α.hom.toRingHom) ≫
        eqToHom (congrArg (fun R : Deformation.CompleteLocalAlgCat.{u, u, u} Λ k =>
          Spec (.of R)) h) ≫ g = f := by
  subst T
  simpa using hf

/-- The quotient map onto an adic truncation commutes with transport along an equality of
complete local algebras. -/
public theorem truncationι_eqToHom
    {Λ : Type u} {k : Type v} [CommRing Λ] [Field k] [Algebra Λ k]
    {R T : Deformation.CompleteLocalAlgCat.{u, w, v} Λ k}
    (h : R = T) (n : ℕ) :
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Deformation.AdicTruncation.ideal R n))) ≫
      eqToHom (congrArg (fun R : Deformation.CompleteLocalAlgCat.{u, w, v} Λ k =>
        Spec (.of R)) h) =
    eqToHom (congrArg (fun R : Deformation.CompleteLocalAlgCat.{u, w, v} Λ k =>
        Spec (.of (Deformation.AdicTruncation.obj R n))) h) ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Deformation.AdicTruncation.ideal T n))) := by
  cases h
  simp
  rfl

end Deformation.Artin

end
