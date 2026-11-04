module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleSmallModelPullbackExact
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.AffinePerfectGeneratorStandardModel
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentDerivedPerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleSchemeAgreementImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CoheratorDecomposition
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RepresentedDerivedFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SmallEtaleStructureSheafPerfect
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.StructureSheafPerfect
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.MapOutOfALocallyConstantComplex

/-!
# The Koszul generator on an affine represented algebraic space

Let `T` be an object of the big fppf site of `S` whose underlying scheme is `Spec A`, and let
`j : T' ⟶ T` be a morphism of the site whose underlying morphism of schemes is an open immersion
with quasi-compact source. Write `Z ⊆ Spec A` for the complement of the image of `j`, a closed
subset with quasi-compact complement, and choose `f₁, …, f_r ∈ A` with `Z = V(f₁, …, f_r)`. The
pullback `K = ε^*K(f₁, …, f_r)` of the sheafified Koszul complex to the small étale site of the
algebraic space `h_T` represented by `T` is

* a perfect object of `D(𝒪_{h_T})`,
* zero on `h_{T'}`, and
* a generator of the objects of `D_QCoh(𝒪_{h_T})` vanishing on `h_{T'}`: such an object `E`
  with `Hom(K[n], E) = 0` for every `n ∈ ℤ` is zero.

This is the affine input of the induction proving Stacks 09IY: the source's proof uses Derived
Categories of Schemes, Lemma 36.15.2 (Stacks 09IR) on the affine member `V` of an elementary
distinguished square "using also Lemma 75.4.2", the comparison of `D_QCoh` of a scheme with
`D_QCoh` of its small étale site (Stacks 071Q).

The proof reads each assertion through `ε^* : D(𝒪_T) ⥤ D(𝒪_{h_T})`. Perfectness: `K` is the image
of the complex obtained by applying the additive right exact functor `M ↦ ε^*(M̃)` to the Koszul
complex, a bounded complex of finite free `A`-modules, and `ε^*(Ã) = 𝒪`; so it is strictly
perfect, hence perfect. Vanishing on `h_{T'}`: `(ε^*E)|_{h_{T'}} = ε^*(j^*E)`
(`AlgebraicGeometry.Space.representedAssociatedModuleEtalePullbackIso`), and the stalks of the
restriction to an open are the stalks at the image points. Generation: an object of
`D_QCoh(𝒪_{h_T})` is `ε^*E'` for `E'` in `D_QCoh(𝒪_T)` (Stacks 071Q), `ε^*` is fully faithful on
`D_QCoh(𝒪_T)` and reflects zero objects (Stacks 08H8), and on `Spec A` the Koszul complex
generates `D_{QCoh,Z}` (Stacks 09IR, `Stacks.Duality.Supported`).

## Main results

* `AlgebraicGeometry.Space.isZero_of_isZero_representedDerivedAssociatedModule`: `ε^*` reflects
  zero objects of `D(𝒪_T)`.
* `AlgebraicGeometry.Scheme.Modules.derivedSupported_compl_range_iff`: for an open immersion `j`
  of schemes, an object of `D(𝒪_Y)` vanishes under `j^*` exactly when its cohomology is supported
  off the image of `j`.
* `AlgebraicGeometry.Space.isPerfect_representedDerivedAssociatedModule_koszulObject`,
  `AlgebraicGeometry.Space.isZero_representedDerivedPullback_koszulObject` and
  `AlgebraicGeometry.Space.isZero_of_forall_hom_representedKoszulObject_eq_zero`: the three
  properties of the Koszul generator listed above — perfect, zero on `h_{T'}`, and generating
  the objects of `D_QCoh(𝒪_{h_T})` that vanish on `h_{T'}`.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Duality Stacks.Duality.Supported Stacks.Koszul.Truncation

universe u

/-- A morphism whose composite with isomorphisms on both sides vanishes is zero. -/
theorem CategoryTheory.Limits.eq_zero_of_iso_comp_comp_iso_eq_zero {C : Type*} [Category* C]
    [HasZeroMorphisms C] {X' X Y Y' : C} (a : X' ≅ X) (b : X ⟶ Y) (c : Y ≅ Y')
    (h : a.hom ≫ b ≫ c.hom = 0) : b = 0 := by
  rw [← cancel_epi a.hom, ← cancel_mono c.hom, Category.assoc, h, comp_zero, zero_comp]

/-! ### Support off the image of an open immersion -/

namespace AlgebraicGeometry.Scheme.Modules

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] AlgebraicGeometry.preservesFiniteLimits_modulesPullback_of_flat
  AlgebraicGeometry.preservesFiniteColimits_modulesPullback AlgebraicGeometry.pullback_additive

variable {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]

/-- **Vanishing under the restriction to an open is support off its image.** For an open
immersion `j : X ⟶ Y`, an object `E` of `D(𝒪_Y)` satisfies `j^*E = 0` exactly when every
cohomology sheaf of `E` has zero stalks at the points of the image of `j`. -/
theorem derivedSupported_compl_range_iff (E : DerivedCategory Y.Modules) :
    derivedSupported Y.ringCatSheaf (Set.range j.base)ᶜ E ↔
      IsZero ((Scheme.Modules.pullback j).mapDerivedCategory.obj E) := by
  have hH : ∀ n : ℤ, (DerivedCategory.homologyFunctor X.Modules n).obj
      ((Scheme.Modules.pullback j).mapDerivedCategory.obj E) ≅
        (Scheme.Modules.restrictFunctor j).obj
          ((DerivedCategory.homologyFunctor Y.Modules n).obj E) := fun n =>
    ((Scheme.Modules.pullback j).mapDerivedCategoryHomologyIso n).app E ≪≫
      ((Scheme.Modules.restrictFunctorIsoPullback j).app _).symm
  rw [DerivedCategory.isZero_iff_forall_isZero_homology]
  refine forall_congr' fun n => ?_
  refine Iff.trans ?_ ⟨fun h => h.of_iso (hH n), fun h => h.of_iso (hH n).symm⟩
  refine ⟨fun h => ?_, fun h x hx => ?_⟩
  · refine Stacks.Cohomology.PushforwardRestriction.isZero_sheafOfModules_of_stalk_isZero
      X.ringCatSheaf _ fun y => ?_
    have hy : j.base y ∉ (Set.range j.base)ᶜ := fun hc => hc ⟨y, rfl⟩
    have hpz := AlgebraicGeometry.SheafOfModules.stalkAddCommGroupFunctor_preservesZeroMorphisms
      Y.ringCatSheaf (j.base y)
    exact IsZero.of_iso (h (j.base y) hy) ((Scheme.Modules.restrictStalkNatIso j y).app _)
  · obtain ⟨y, rfl⟩ := not_not.1 hx
    have hpz := AlgebraicGeometry.SheafOfModules.stalkAddCommGroupFunctor_preservesZeroMorphisms
      X.ringCatSheaf y
    exact IsZero.of_iso
      (Functor.map_isZero (SheafOfModules.stalkAddCommGroupFunctor X.ringCatSheaf y) h)
      ((Scheme.Modules.restrictStalkNatIso j y).app _).symm

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance]
  _root_.AlgebraicGeometry.SmallEtale.preservesFiniteLimits_associatedModule

attribute [local instance] AlgebraicGeometry.preservesFiniteLimits_modulesPullback_of_flat
  AlgebraicGeometry.preservesFiniteColimits_modulesPullback AlgebraicGeometry.pullback_additive

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### `ε^*` reflects zero objects -/

/-- **`ε^* : D(𝒪_T) ⥤ D(𝒪_{h_T})` reflects zero objects** (the zero-detection assertion of
Stacks 08H8, on cohomology sheaves): `ε^*` commutes with cohomology, and the associated module of
a sheaf of `𝒪_T`-modules vanishes only if the sheaf does. -/
theorem isZero_of_isZero_representedDerivedAssociatedModule (T : BigFppfOver B S hS)
    (E : DerivedCategory ((BigFppfOver.toScheme B S hS).obj T).Modules)
    (h : IsZero ((representedDerivedAssociatedModule B S hS T).obj E)) : IsZero E := by
  rw [DerivedCategory.isZero_iff_forall_isZero_homology]
  intro n
  have h₁ : IsZero ((representedAssociatedModule B S hS T (isAlgebraicSpace_yoneda B S hS T)).obj
      ((DerivedCategory.homologyFunctor _ n).obj E)) :=
    IsZero.of_iso (Functor.map_isZero _ h)
      (((representedAssociatedModule B S hS T
        (isAlgebraicSpace_yoneda B S hS T)).mapDerivedCategoryHomologyIso n).app E).symm
  have h₂ := IsZero.of_iso ((representedSmallEtaleModuleEquivalence B S hS T).inverse.map_isZero h₁)
    ((representedSmallEtaleModuleEquivalence B S hS T).unitIso.app _)
  exact _root_.AlgebraicGeometry.SmallEtale.isZero_of_isZero_associatedModule_general
    (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj T) T.left.property _ h₂

/-! ### Restriction to an open of the represented space -/

variable {T' T : BigFppfOver B S hS} (j : T' ⟶ T)
  [_root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map j)]
  (hj : IsEtale B S hS (representedSpaceMap B S hS j).hom)

/-- `ε^*` on a represented algebraic space is additive. -/
private instance additive_representedDerivedAssociatedModule (T : BigFppfOver B S hS) :
    (representedDerivedAssociatedModule B S hS T).Additive := by
  unfold representedDerivedAssociatedModule; infer_instance

/-- **Vanishing of `(ε^*E)|_{h_{T'}}` is support of `E` off the image of `T'`.** For a morphism
`j : T' ⟶ T` of the site which is an open immersion of schemes, `(ε^*E)|_{h_{T'}} = ε^*(j^*E)`,
`ε^*` reflects zero objects, and `j^*E = 0` is support off the image. -/
theorem isZero_representedDerivedPullback_associatedModule_iff
    (E : DerivedCategory ((BigFppfOver.toScheme B S hS).obj T).Modules) :
    IsZero ((representedDerivedPullback B S hS j hj).obj
        ((representedDerivedAssociatedModule B S hS T).obj E)) ↔
      derivedSupported ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf
        (Set.range ((BigFppfOver.toScheme B S hS).map j).base)ᶜ E := by
  have := etaleModulePullback_additive.{u, u} B S hS (representedSpaceMap B S hS j) hj
  have := preservesFiniteLimits_etaleModulePullback B S hS (representedSpaceMap B S hS j) hj
  have := preservesFiniteColimits_etaleModulePullback B S hS (representedSpaceMap B S hS j) hj
  let e := Functor.mapDerivedCategorySquareIso
    (representedAssociatedModuleEtalePullbackIso B S hS j hj)
  rw [Scheme.Modules.derivedSupported_compl_range_iff]
  refine (⟨fun h => h.of_iso (e.app E).symm, fun h => h.of_iso (e.app E)⟩ :
    _ ↔ _).trans ⟨fun h => ?_, fun h => ?_⟩
  · exact isZero_of_isZero_representedDerivedAssociatedModule B S hS T' _ h
  · exact Functor.map_isZero (representedDerivedAssociatedModule B S hS T') h

/-- **Vanishing of `(ε^*E)|_{h_O}` for an open `O` of the scheme of `T` is support of `E` in the
complement of `O`.** -/
theorem isZero_representedDerivedPullback_openSubHom_iff (T : BigFppfOver B S hS)
    (O : ((BigFppfOver.toScheme B S hS).obj T).Opens)
    (E : DerivedCategory ((BigFppfOver.toScheme B S hS).obj T).Modules) :
    IsZero ((representedDerivedPullback B S hS (openSubHom T O)
        (isEtale_representedSpaceMap_openSubHom B S hS T O)).obj
        ((representedDerivedAssociatedModule B S hS T).obj E)) ↔
      derivedSupported ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf
        ((O : Set ((BigFppfOver.toScheme B S hS).obj T))ᶜ) E := by
  have : _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (openSubHom T O)) :=
    (toScheme_map_openSubHom B S hS T O).symm ▸
      (inferInstance : _root_.AlgebraicGeometry.IsOpenImmersion O.ι)
  have hset : (Set.range ((BigFppfOver.toScheme B S hS).map (openSubHom T O)).base)ᶜ =
      (O : Set ((BigFppfOver.toScheme B S hS).obj T))ᶜ := by
    rw [toScheme_map_openSubHom]
    exact congrArg compl (Scheme.Opens.range_ι O)
  exact hset ▸ isZero_representedDerivedPullback_associatedModule_iff B S hS (openSubHom T O)
    (isEtale_representedSpaceMap_openSubHom B S hS T O) E


/-! ### The Koszul generator -/

section Koszul

variable {A : Type u} [CommRing A] (hA : B.Contains (Spec (CommRingCat.of A)))
  (p : Spec (CommRingCat.of A) ⟶ S)

/-- **The pullback to `h_{Spec A}` of the sheafified Koszul complex is perfect.** It is the image
of the complex obtained from the Koszul complex, a bounded complex of finite free `A`-modules, by
the additive right exact functor `M ↦ ε^*(M̃)`, which carries `A` to the structure sheaf; that
complex is strictly perfect, hence perfect. -/
theorem isPerfect_representedDerivedAssociatedModule_koszulObject {r : ℕ} (f : Fin r → A) :
    (smallEtaleRingedSite B S hS (yoneda.obj (BigFppfOver.mk B S hS hA p))
        (isAlgebraicSpace_yoneda B S hS _)).IsPerfect
      ((representedDerivedAssociatedModule B S hS (BigFppfOver.mk B S hS hA p)).obj
        (koszulObject f)) := by
  let T := BigFppfOver.mk B S hS hA p
  let ε : (Spec (CommRingCat.of A)).Modules ⥤
      Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T) :=
    representedAssociatedModule B S hS T (isAlgebraicSpace_yoneda B S hS T)
  let Φ : ModuleCat.{u} A ⥤
      Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T) :=
    tilde.functor (CommRingCat.of A) ⋙ ε
  have : PreservesFiniteColimits (tilde.functor (CommRingCat.of A)) :=
    Stacks.AffineTilde.preservesFiniteColimits_tildeFunctor (CommRingCat.of A)
  have : (tilde.functor (CommRingCat.of A)).Additive := ⟨by intros; exact tilde.map_add _ _⟩
  have : ε.Additive := additive_representedAssociatedModule B S hS T _
  have : PreservesFiniteColimits ε :=
    preservesFiniteColimits_representedAssociatedModule B S hS T _
  have : Φ.Additive := inferInstanceAs (tilde.functor (CommRingCat.of A) ⋙ ε).Additive
  have : PreservesFiniteLimits (tilde.functor (CommRingCat.of A)) :=
    AlgebraicGeometry.tilde.preservesFiniteLimits _
  have : PreservesFiniteLimits ε := preservesFiniteLimits_representedAssociatedModule B S hS T _
  have : PreservesFiniteColimits Φ := comp_preservesFiniteColimits _ _
  let e : Φ.obj (ModuleCat.of A A) ≅ SheafOfModules.unit _ :=
    ε.mapIso tildeSelf ≪≫ (representedModulePushforward B S hS T).mapIso
      (@asIso _ _ _ _ _ (_root_.AlgebraicGeometry.SmallEtale.isIso_pullbackObjUnitToUnit
        (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj T) T.left.property))
  let C := (Koszul.seqComplex f).extend ComplexShape.embeddingDownNat
  have hb : {i : ℤ | ¬ IsZero (C.X i)}.Finite := by
    refine Set.Finite.subset (Set.finite_Icc (-(r : ℤ)) 0) fun i hi => ?_
    simp only [Set.mem_ofPred_eq] at hi
    refine Set.mem_Icc.2 ⟨?_, ?_⟩ <;> by_contra hcon
    · exact hi (Stacks.AffineTilde.isZero_extend_seqComplex_X_of_lt_or_lt (R := CommRingCat.of A)
        f i (Or.inl (by lia)))
    · exact hi (Stacks.AffineTilde.isZero_extend_seqComplex_X_of_lt_or_lt (R := CommRingCat.of A)
        f i (Or.inr (by lia)))
  have hsp := Stacks.SheafOfModules.isStrictlyPerfect_mapHomologicalComplex_of_finite_projective
    Φ e hb
    (fun i => (Stacks.AffineTilde.finite_free_extend_seqComplex_X (R := CommRingCat.of A) f i).1)
    (fun i => have :=
        (Stacks.AffineTilde.finite_free_extend_seqComplex_X (R := CommRingCat.of A) f i).2
      Module.Projective.of_free)
  refine ⟨(Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj C,
    RingedSite.isPerfectComplex_of_isStrictlyPerfect _ _ hsp, ⟨?_⟩⟩
  exact DerivedCategory.Q.mapIso
      ((Functor.mapHomologicalComplexCompIso (Iso.refl Φ) (ComplexShape.up ℤ)).app C).symm ≪≫
    (ε.mapDerivedCategoryFactors.app _).symm

/-- **The sheafified Koszul complex on `Spec A` lies in `D_QCoh`, at the standard model**: this is
`Stacks.Duality.Supported.derivedQuasiCoherent_koszulObject`, read through the comparison of the
locally small and the standard model, which preserves cohomology objects. -/
theorem derivedQuasiCoherent_koszulObject_standard {r : ℕ} (f : Fin r → A) :
    Stacks.Duality.derivedQuasiCoherent (Spec (CommRingCat.of A)) (koszulObject.{u + 1} f) := by
  let hls : HasDerivedCategory.{u} (Spec (CommRingCat.of A)).Modules :=
    AlgebraicGeometry.Scheme.Modules.hasDerivedCategory _
  let hst := HasDerivedCategory.standard (Spec (CommRingCat.of A)).Modules
  let P : ObjectProperty (Spec (CommRingCat.of A)).Modules :=
    SheafOfModules.isQuasicoherent (Spec (CommRingCat.of A)).ringCatSheaf
  let : P.IsClosedUnderIsomorphisms := inferInstanceAs (SheafOfModules.isQuasicoherent
    (Spec (CommRingCat.of A)).ringCatSheaf).IsClosedUnderIsomorphisms
  exact fun n => P.prop_of_iso ((@DerivedCategory.homologyFunctor _ _ _ hst n).mapIso
    ((StacksDraft.DerivedModel.modelCompQIso hls hst).app _))
    ((StacksDraft.DerivedModel.derivedCategoryB_modelEquiv_functor_obj_iff P hls hst
      (@koszulObject A _ r hls f)).2 (derivedQuasiCoherent_koszulObject f) n)

variable {hA p} in
/-- **The pullback of the Koszul complex vanishes on the open `⋃ D(f_i)`.** For `j : T' ⟶ T` an
open immersion of schemes onto `⋃ D(f_i)`, the restriction to `h_{T'}` of `ε^*K(f)` is
`ε^*(j^*K(f))`, and `K(f)` is supported on `V(f₁, …, f_r)`. -/
theorem isZero_representedDerivedPullback_koszulObject {r : ℕ} (f : Fin r → A)
    {T' : BigFppfOver B S hS} (j : T' ⟶ BigFppfOver.mk B S hS hA p)
    [_root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map j)]
    (hj : IsEtale B S hS (representedSpaceMap B S hS j).hom)
    (hrange : Set.range ((BigFppfOver.toScheme B S hS).map j).base =
      (Stacks.Koszul.Truncation.openComplement f : Set (Spec (CommRingCat.of A)))) :
    IsZero ((representedDerivedPullback B S hS
        j hj).obj
      ((representedDerivedAssociatedModule B S hS (BigFppfOver.mk B S hS hA p)).obj
        (koszulObject f))) := by
  refine (isZero_representedDerivedPullback_associatedModule_iff B S hS j hj _).2 ?_
  rw [hrange]
  exact
    (derivedSupported_of_isZero_derivedRestrict_standard _ _ (compl_compl _).subset _
      (Stacks.Koszul.OpenComplement.isZero_derivedRestrict_koszulObject f))

variable {hA p} in
/-- **The pullback of the Koszul complex generates the objects of `D_QCoh(𝒪_{h_{Spec A}})`
vanishing on `⋃ D(f_i)`.** An object `E` of `D_QCoh(𝒪_{h_{Spec A}})` whose restriction to the
represented open `⋃ D(f_i)` vanishes and which receives only zero maps from the shifts of
`ε^*K(f₁, …, f_r)` is zero.

`E = ε^*E'` with `E'` in `D_QCoh(𝒪_{Spec A})` (Stacks 071Q); `E'` is supported on
`V(f₁, …, f_r)` because `ε^*` commutes with restriction to opens and reflects zero objects; a
morphism `K(f)[n] ⟶ E'` is zero because its image under the fully faithful `ε^*` is; and the
Koszul complex generates `D_{QCoh,V(f)}(𝒪_{Spec A})` (Stacks 09IR). -/
theorem isZero_of_forall_hom_representedKoszulObject_eq_zero {r : ℕ} (f : Fin r → A)
    {T' : BigFppfOver B S hS} (j : T' ⟶ BigFppfOver.mk B S hS hA p)
    [_root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map j)]
    (hj : IsEtale B S hS (representedSpaceMap B S hS j).hom)
    (hrange : Set.range ((BigFppfOver.toScheme B S hS).map j).base =
      (Stacks.Koszul.Truncation.openComplement f : Set (Spec (CommRingCat.of A))))
    (E : DerivedCategory (Modules.{u, u} B S hS (yoneda.obj (BigFppfOver.mk B S hS hA p))
      (isAlgebraicSpace_yoneda B S hS _)))
    (hE : qcohDerivedProp B S hS ⟨_, isAlgebraicSpace_yoneda B S hS (BigFppfOver.mk B S hS hA p)⟩ E)
    (hEU : IsZero ((representedDerivedPullback B S hS
        j hj).obj E))
    (h : ∀ (n : ℤ) (g : ((representedDerivedAssociatedModule B S hS
        (BigFppfOver.mk B S hS hA p)).obj (koszulObject f))⟦n⟧ ⟶ E), g = 0) :
    IsZero E := by
  obtain ⟨ω, hω, ⟨e⟩⟩ : ∃ ω : DerivedCategory (Spec (CommRingCat.of A)).Modules,
      (∀ i : ℤ, ((DerivedCategory.homologyFunctor _ i).obj ω).IsQuasicoherent) ∧
        Nonempty ((representedDerivedAssociatedModule B S hS (BigFppfOver.mk B S hS hA p)).obj ω ≅
          E) :=
    exists_representedDerivedAssociatedModule_iso B S hS (BigFppfOver.mk B S hS hA p) E hE
  have hωqc : Stacks.Duality.derivedQuasiCoherent (Spec (CommRingCat.of A)) ω := hω
  -- `ω` is supported on the complement of `⋃ D(f_i)`.
  have hsupp : derivedSupported (Spec (CommRingCat.of A)).ringCatSheaf
      (((Stacks.Koszul.Truncation.openComplement f : (Spec (CommRingCat.of A)).Opens) :
        Set (Spec (CommRingCat.of A)))ᶜ) ω := by
    have := (isZero_representedDerivedPullback_associatedModule_iff B S hS j hj ω).1
      (hEU.of_iso ((representedDerivedPullback B S hS _ _).mapIso e))
    rwa [hrange] at this
  -- Every morphism from a shift of the Koszul complex to `ω` vanishes.
  have hK := derivedQuasiCoherent_koszulObject_standard f
  have hWS := Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerre
    (Spec (CommRingCat.of A))
  have := DerivedCategoryB.derivedCategoryB_isStableUnderShift _ hWS
  have hhom : ∀ (n : ℤ) (g : (koszulObject f)⟦n⟧ ⟶ ω), g = 0 := by
    intro n g
    have hKn : representedSchemeDerivedQcoh B S hS (BigFppfOver.mk B S hS hA p)
        ((koszulObject f)⟦n⟧) :=
      ObjectProperty.le_shift (P := Stacks.Duality.derivedQuasiCoherent (Spec (CommRingCat.of A)))
        n _ hK
    refine eq_zero_of_representedDerivedAssociatedModule_map_eq_zero B S hS
      (BigFppfOver.mk B S hS hA p) hKn hω g ?_
    have :
        (representedDerivedAssociatedModule B S hS (BigFppfOver.mk B S hS hA p)).CommShift ℤ := by
      unfold representedDerivedAssociatedModule; infer_instance
    have h0 := h n
      (((representedDerivedAssociatedModule B S hS (BigFppfOver.mk B S hS hA p)).commShiftIso
        n).inv.app (koszulObject f) ≫
          (representedDerivedAssociatedModule B S hS (BigFppfOver.mk B S hS hA p)).map g ≫ e.hom)
    exact eq_zero_of_iso_comp_comp_iso_eq_zero
      (((representedDerivedAssociatedModule B S hS (BigFppfOver.mk B S hS hA p)).commShiftIso
        n).app (koszulObject f)).symm
      ((representedDerivedAssociatedModule B S hS (BigFppfOver.mk B S hS hA p)).map g) e h0
  exact IsZero.of_iso
    ((Functor.map_isZero (representedDerivedAssociatedModule B S hS (BigFppfOver.mk B S hS hA p))
      (isZero_of_derivedSupported_of_forall_hom_koszulObject_eq_zero f ω hωqc hsupp hhom))) e.symm

end Koszul

end AlgebraicGeometry.Space

end
