module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.HomBijection.BaseIdealSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealBijection
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdeals
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceRange
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.HomBijection.CompletionFullyFaithfulProperSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPowerModuleCoherent
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ImageSubsheafUniversal
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversalFirstOrderThickening
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperMorphismSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.FormalAlgebraization
public import StacksFrontier.AlgebraicGeometry.Spaces.SpecQuotientOverAffineBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.CompletionFullyFaithfulProperSupport

/-!
# The adic fibres of an algebraic space as closed subspaces

Let `A` be a ring, `I ⊆ A` an ideal and `P` an algebraic space over `Spec A`. The `n`-th adic
fibre `P_n = P ×_{Spec A} Spec (A / I^{n+1})` is the inverse image in `P` of the closed subscheme
`Spec (A / I^{n+1})` of the base, so it is a closed subspace of `P`. Its defining ideal sheaf is
`I^{n+1} 𝒪_P`: on an affine étale chart `U = Spec R` of `P` the inverse image is
`Spec (R / I^{n+1} R)`.

## Main definitions

* `AlgebraicGeometry.Space.adicThickeningSubspace`: the closed subspace `Spec (A / I^{n+1})` of
  the base.
* `AlgebraicGeometry.Space.adicFibreSubspace`: its inverse image in an algebraic space over the
  base.

## Main results

* `AlgebraicGeometry.Space.range_adicFibre_fst`: the adic fibre is the inverse image, as a
  subfunctor.
* `AlgebraicGeometry.Space.definingIdealSheaf_adicFibreSubspace`: the defining ideal sheaf of the
  adic fibre is `I^{n+1} 𝒪_P`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (A : Type u) [CommRing A] (I : Ideal A) (B : BigFppfSite.{u})
  (hS : B.Contains (Spec (.of A))) (hSn : ∀ n, B.Contains (adicThickening A I n))

local notation "𝒯" => BigFppfOver.toScheme B (Spec (CommRingCat.of A)) hS

/-- The `n`-th adic thickening of the base is a closed immersion of schemes. -/
theorem isClosedImmersion_toScheme_map_adicThickeningMap (n : ℕ) :
    _root_.AlgebraicGeometry.IsClosedImmersion ((𝒯).map (adicThickeningMap A I B hS hSn n)) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

/-- **The closed subspace `Spec (A / I^{n+1})` of the base.** -/
def adicThickeningSubspace (n : ℕ) :
    ClosedSubspaces B (Spec (.of A)) hS (yoneda.obj (baseObject A B hS)) :=
  ⟨Subfunctor.range (yoneda.map (adicThickeningMap A I B hS hSn n)),
    isClosedSubspace_range_yoneda_map B _ hS _
      (isClosedImmersion_toScheme_map_adicThickeningMap A I B hS hSn n)⟩

/-- **The `n`-th adic fibre of an algebraic space over the base, as a closed subspace**: the
inverse image of `Spec (A / I^{n+1})`. -/
def adicFibreSubspace (P : AlgebraicSpaces B (Spec (.of A)) hS)
    (f : P.1 ⟶ yoneda.obj (baseObject A B hS)) (n : ℕ) :
    ClosedSubspaces B (Spec (.of A)) hS P.1 :=
  ⟨(adicThickeningSubspace A I B hS hSn n).1.preimage f,
    isClosedSubspace_preimage B _ hS f _ (isAlgebraicSpace_yoneda B _ hS _) P.2
      (adicThickeningSubspace A I B hS hSn n).2⟩

/-- The adic fibre, as a subfunctor, is the range of the projection from the fibre product. -/
theorem range_adicFibre_fst {P : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u}
    (f : P ⟶ yoneda.obj (baseObject A B hS)) (n : ℕ) :
    Subfunctor.range (pullback.fst f (yoneda.map (adicThickeningMap A I B hS hSn n))) =
      (Subfunctor.range (yoneda.map (adicThickeningMap A I B hS hSn n))).preimage f :=
  Subfunctor.range_eq_preimage_of_isPullback (IsPullback.of_hasPullback _ _)

/-- An element of `A` dies in `Spec (A / I^{n+1})`'s global functions iff it lies in `I^{n+1}`. -/
private theorem appTop_adicThickeningMap_eq_zero_iff (n : ℕ) (a : A) :
    ((𝒯).map (adicThickeningMap A I B hS hSn n)).appTop.hom
      ((Scheme.ΓSpecIso (.of A)).inv.hom a) = 0 ↔ a ∈ I ^ (n + 1) := by
  have h1 := congrArg (fun φ => φ.hom a) (Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))) : CommRingCat.of A ⟶ _))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h1
  refine ⟨fun h2 => Ideal.Quotient.eq_zero_iff_mem.1 ?_, fun h2 => h1.symm.trans ?_⟩
  · have h3 : (Scheme.ΓSpecIso (CommRingCat.of (A ⧸ I ^ (n + 1)))).inv.hom
        (Ideal.Quotient.mk (I ^ (n + 1)) a) = 0 := h1.trans h2
    have := congrArg (Scheme.ΓSpecIso _).hom.hom h3
    rwa [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply, map_zero] at this
  · rw [Ideal.Quotient.eq_zero_iff_mem.2 h2, map_zero]
    rfl

/-- **A morphism to the base factors through `Spec (A / I^{n+1})` once `I^{n+1}` dies on its
global functions.** -/
theorem exists_comp_eq_adicThickeningMap (n : ℕ) {T : BigFppfOver B (Spec (.of A)) hS}
    (k : T ⟶ baseObject A B hS)
    (h : ∀ a ∈ I ^ (n + 1), ((Scheme.ΓSpecIso (.of A)).inv ≫ ((𝒯).map k).appTop).hom a = 0) :
    ∃ t : T ⟶ adicThickeningObject A I B hS hSn n, t ≫ adicThickeningMap A I B hS hSn n = k := by
  have := isClosedImmersion_toScheme_map_adicThickeningMap A I B hS hSn n
  have : IsAffine ((𝒯).obj (baseObject A B hS)) :=
    inferInstanceAs (IsAffine (Spec (.of A)))
  refine exists_comp_eq_of_ker_le B _ hS _ k inferInstance ?_
  rw [Scheme.ker_le_ker_iff_of_isAffine]
  intro x hx
  rw [RingHom.mem_ker] at hx ⊢
  obtain ⟨a, rfl⟩ : ∃ a, (Scheme.ΓSpecIso (.of A)).inv.hom a = x :=
    ⟨(Scheme.ΓSpecIso (.of A)).hom.hom x, by
      rw [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]⟩
  exact h a ((appTop_adicThickeningMap_eq_zero_iff A I B hS hSn n a).1 hx)

/-- Two morphisms into the base object agree. -/
theorem eq_of_hom_baseObject {T : BigFppfOver B (Spec (.of A)) hS}
    (a b : T ⟶ baseObject A B hS) : a = b :=
  Over.mkIdTerminal.hom_ext a b

/-- The underlying morphism of schemes of a morphism to the base object is the structure
morphism of its source. -/
theorem toScheme_map_hom_baseObject {T : BigFppfOver B (Spec (.of A)) hS}
    (k : T ⟶ baseObject A B hS) : (𝒯).map k = B.inclusion.map T.hom := by
  have h := congrArg B.inclusion.map (Over.w k)
  simp only [baseObject, Over.mk_hom] at h
  exact h

/-- A morphism of presheaves from a representable presheaf lands in the adic fibre subspace as
soon as its source maps to `Spec (A / I^{n+1})`. -/
theorem range_le_adicFibreSubspace (P : AlgebraicSpaces B (Spec (.of A)) hS)
    (f : P.1 ⟶ yoneda.obj (baseObject A B hS)) (n : ℕ) {T : BigFppfOver B (Spec (.of A)) hS}
    (g : yoneda.obj T ⟶ P.1) (t : T ⟶ adicThickeningObject A I B hS hSn n) :
    Subfunctor.range g ≤ (adicFibreSubspace A I B hS hSn P f n).1 := by
  rintro W _ ⟨h, rfl⟩
  change (f.app W (g.app W h)) ∈ Set.range ((yoneda.map (adicThickeningMap A I B hS hSn n)).app W)
  exact ⟨h ≫ t, eq_of_hom_baseObject A B hS _ _⟩

/-- The ring map from `A` to the global functions of an object of the site over `Spec A`. -/
abbrev baseFunctionsHom (T : BigFppfOver B (Spec (.of A)) hS) : A →+* Γ((𝒯).obj T, ⊤) :=
  ((Scheme.ΓSpecIso (.of A)).inv ≫ (B.inclusion.map T.hom).appTop).hom

/-- On an affine étale chart `U = Spec R` of `P`, the closed immersion `P_n ×_P U ⟶ U` kills no
more than `I^{n+1} R`: the closed subscheme of `U` cut out by `I^{n+1} R` maps to `P_n`. -/
theorem ker_appTop_adicFibreSubspace_snd_le (P : AlgebraicSpaces B (Spec (.of A)) hS)
    (f : P.1 ⟶ yoneda.obj (baseObject A B hS)) (n : ℕ) (U : SmallEtale B (Spec (.of A)) hS P.1)
    [IsAffine ((𝒯).obj U.1.left)] :
    RingHom.ker ((𝒯).map ((adicFibreSubspace A I B hS hSn P f n).2.2.rep.snd U.1.hom)).appTop.hom ≤
      Ideal.map (baseFunctionsHom A B hS U.1.left) (I ^ (n + 1)) := by
  set Z := adicFibreSubspace A I B hS hSn P f n
  have sq := Z.2.2.rep.isPullback U.1.hom
  set J' : Ideal Γ((𝒯).obj U.1.left, ⊤) :=
    Ideal.map (baseFunctionsHom A B hS U.1.left) (I ^ (n + 1))
  set q := specQuotientSiteHom B _ hS U.1.left J'
  obtain ⟨t, -⟩ := exists_comp_eq_adicThickeningMap A I B hS hSn n
    (Over.mkIdTerminal.from (specQuotientOverSite B _ hS U.1.left J')) (by
      intro a ha
      rw [toScheme_map_hom_baseObject]
      have hw : B.inclusion.map (specQuotientOverSite B _ hS U.1.left J').hom =
          (𝒯).map q ≫ B.inclusion.map U.1.left.hom := by
        have := congrArg B.inclusion.map (Over.w q)
        rw [Functor.map_comp] at this
        exact this.symm
      rw [hw, Scheme.Hom.comp_appTop, ← Category.assoc, CommRingCat.hom_comp,
        RingHom.comp_apply]
      exact (ker_appTop_specQuotientSiteHom B _ hS U.1.left J').ge
        (Ideal.mem_map_of_mem _ ha))
  have hle := range_le_adicFibreSubspace A I B hS hSn P f n (yoneda.map q ≫ U.1.hom) t
  let k : specQuotientOverSite B _ hS U.1.left J' ⟶ Z.2.2.rep.pullback U.1.hom :=
    yoneda.preimage (sq.lift (Subfunctor.lift _ hle) (yoneda.map q) (Subfunctor.lift_ι _ _))
  have hk : k ≫ Z.2.2.rep.snd U.1.hom = q := yoneda.map_injective (by
    rw [Functor.map_comp, Functor.map_preimage, IsPullback.lift_snd])
  refine (ker_appTop_le_comp ((𝒯).map k) _).trans_eq ?_
  rw [← Functor.map_comp, hk, ker_appTop_specQuotientSiteHom]


/-- On any étale chart `U` of `P`, the elements of `I^{n+1}` die on `P_n ×_P U`, which maps to
`Spec (A / I^{n+1})`. -/
theorem le_ker_appTop_adicFibreSubspace_snd (P : AlgebraicSpaces B (Spec (.of A)) hS)
    (f : P.1 ⟶ yoneda.obj (baseObject A B hS)) (n : ℕ) (U : SmallEtale B (Spec (.of A)) hS P.1) :
    Ideal.map (baseFunctionsHom A B hS U.1.left) (I ^ (n + 1)) ≤
      RingHom.ker
        ((𝒯).map ((adicFibreSubspace A I B hS hSn P f n).2.2.rep.snd U.1.hom)).appTop.hom := by
  set Z := adicFibreSubspace A I B hS hSn P f n
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  change ((𝒯).map (Z.2.2.rep.snd U.1.hom)).appTop.hom (baseFunctionsHom A B hS U.1.left a) = 0
  have hmem : (Z.2.2.rep.fst U.1.hom ≫ Z.1.ι ≫ f).app (op (Z.2.2.rep.pullback U.1.hom))
      (𝟙 _) ∈ Set.range ((yoneda.map (adicThickeningMap A I B hS hSn n)).app
        (op (Z.2.2.rep.pullback U.1.hom))) :=
    ((Z.2.2.rep.fst U.1.hom).app (op (Z.2.2.rep.pullback U.1.hom))
      (𝟙 (Z.2.2.rep.pullback U.1.hom))).2
  obtain ⟨t, -⟩ := hmem
  have hσ : B.inclusion.map (Z.2.2.rep.pullback U.1.hom).hom =
      (𝒯).map t ≫ (𝒯).map (adicThickeningMap A I B hS hSn n) := by
    rw [← Functor.map_comp, toScheme_map_hom_baseObject]
  have hw : (𝒯).map (Z.2.2.rep.snd U.1.hom) ≫ B.inclusion.map U.1.left.hom =
      B.inclusion.map (Z.2.2.rep.pullback U.1.hom).hom :=
    (B.inclusion.map_comp _ _).symm.trans (congrArg B.inclusion.map (Over.w _))
  have e1 : (B.inclusion.map U.1.left.hom).appTop ≫ ((𝒯).map (Z.2.2.rep.snd U.1.hom)).appTop =
      ((𝒯).map (adicThickeningMap A I B hS hSn n)).appTop ≫ ((𝒯).map t).appTop := by
    rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, hw, hσ]
  have e2 := (appTop_adicThickeningMap_eq_zero_iff A I B hS hSn n a).2 ha
  have e3 := congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)) e1
  simpa only [CommRingCat.hom_comp, RingHom.comp_apply, e2, map_zero] using e3

/-- **The defining ideal sheaf of the adic fibre `P_n` is `I^{n+1} 𝒪_P`.** -/
theorem definingIdealSheaf_adicFibreSubspace (P : AlgebraicSpaces B (Spec (.of A)) hS)
    (f : P.1 ⟶ yoneda.obj (baseObject A B hS)) (n : ℕ) :
    definingIdealSheaf B _ hS P (adicFibreSubspace A I B hS hSn P f n) =
      C1573.baseIdealSubmodule P.1 P.2 (I ^ (n + 1)) := by
  refine structureSubmodule_ext_of_forall_isAffine B _ hS P _ _ fun U hU => ?_
  have : IsAffine ((𝒯).obj U.1.left) := hU
  have h₁ := C1573.chartIdeal_baseIdealSubmodule_of_isAffine (hX := P.2) (I ^ (n + 1)) U hU
  rw [definingIdealSheaf_obj, definingIdealAt_eq_ker]
  refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
  · have := ker_appTop_adicFibreSubspace_snd_le A I B hS hSn P f n U hx
    change x ∈ chartIdeal B _ hS P (C1573.baseIdealSubmodule P.1 P.2 (I ^ (n + 1))) U
    rw [h₁]
    exact this
  · change x ∈ chartIdeal B _ hS P (C1573.baseIdealSubmodule P.1 P.2 (I ^ (n + 1))) U at hx
    rw [h₁] at hx
    exact le_ker_appTop_adicFibreSubspace_snd A I B hS hSn P f n U hx

section Krull

attribute [local instance] pointTopology
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

/-- **A closed subspace of a proper algebraic space containing every adic fibre is everything.**
Let `A` be a Noetherian ring complete with respect to `I` and `X` proper over `Spec A`. If a
closed subspace `C ⊆ X` contains every `X_n`, its ideal sheaf `𝒦` lies in every `I^{n+1} 𝒪_X`, so
the completion of the inclusion `𝒦 ⟶ 𝒪_X` vanishes; completion is faithful on coherent modules
whose supports meet properly over `Spec A` (Stacks 08B9), so `𝒦 = 0` and `C = X`. -/
theorem eq_top_of_forall_adicFibreSubspace_le [IsNoetherianRing A] [IsAdicComplete I A]
    (X : AlgebraicSpaces B (Spec (.of A)) hS) (f : X ⟶ schemeSpace (baseObject A B hS))
    (hf : IsProper B _ hS f.hom) (C : ClosedSubspaces B _ hS X.1)
    (hC : ∀ n, (adicFibreSubspace A I B hS hSn X f.hom n).1 ≤ C.1) : C.1 = ⊤ := by
  have hlft : IsLocallyOfFiniteType B _ hS f.hom := hf.2.1.1
  let := C1573.fact_isLocallyNoetherian_of_baseObject X f hlft
  let 𝒦 : (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B _ hS X.1 X.2).O)).Submodule := definingIdealSheaf B _ hS X C
  have hK : ∀ n, 𝒦 ≤ C1573.baseIdealSubmodule X.1 X.2 (I ^ (n + 1)) := fun n => by
    have h := definingIdealSheaf_antitone B _ hS X _ _ (hC n)
    rwa [definingIdealSheaf_adicFibreSubspace A I B hS hSn X f.hom n] at h
  have hKc : IsCoherent B _ hS X.1 X.2 𝒦.toSheafOfModules :=
    isCoherent_idealSheaf B _ hS X.1 X.2 𝒦 (isQuasicoherentOnSite_definingIdealSheaf B _ hS X C)
  let F : CoherentModules B _ hS X.1 X.2 := ⟨𝒦.toSheafOfModules, hKc⟩
  let G : CoherentModules B _ hS X.1 X.2 :=
    ⟨SheafOfModules.unit _, isCoherent_structureSheaf B _ hS X.1 X.2⟩
  let ι : F ⟶ G := ObjectProperty.homMk 𝒦.ι
  let z : F ⟶ G := ObjectProperty.homMk 0
  -- the inclusion dies modulo every `I^{n+1}`
  have hπ : ∀ n, 𝒦.ι ≫ cokernel.π (idealPowerMultiple B _ hS X.1 X.2
      (C1573.baseIdealSubmodule X.1 X.2 I) (n + 1) (SheafOfModules.unit _)).ι = 0 := fun n => by
    have h1 : 𝒦.ι ≫ idealQuotientπ (baseRingHom A B hS X.1 X.2) (SheafOfModules.unit _)
        (I ^ (n + 1)) = 0 := by
      have hle : C1573.baseIdealSubmodule X.1 X.2 (I ^ (n + 1)) ≤ SheafOfModules.Submodule.ker
          (idealQuotientπ (baseRingHom A B hS X.1 X.2) (SheafOfModules.unit _) (I ^ (n + 1))) :=
        Stacks.SheafOfModules.ImageSubsheaf.imageSubmodule_le _ fun U m =>
          (SheafOfModules.Submodule.mem_ker _ U _).2 (by
            change ((idealMultipleι (baseRingHom A B hS X.1 X.2) (SheafOfModules.unit _)
              (I ^ (n + 1)) ≫ idealQuotientπ (baseRingHom A B hS X.1 X.2)
                (SheafOfModules.unit _) (I ^ (n + 1))).val.app U) m = 0
            rw [cokernel.condition]
            rfl)
      ext U x
      exact hle U (hK n U x.2)
    have h2 := C1573.smallEtaleAdicQuotientProjection_baseIdealQuotientIso_hom
      (SheafOfModules.unit _) I (n + 1) (X := X.1) (hX := X.2)
    rw [← h2, ← Category.assoc] at h1
    exact (Iso.cancel_iso_hom_right _ _ _).1 (h1.trans (zero_comp).symm)
  have hcomp : (completionFunctor B _ hS X.1 X.2 (C1573.baseIdealSubmodule X.1 X.2 I)
      (C1573.isQuasicoherentOnSite_baseIdealSubmodule (X := X.1) (hX := X.2) I)).map ι =
      (completionFunctor B _ hS X.1 X.2 (C1573.baseIdealSubmodule X.1 X.2 I)
        (C1573.isQuasicoherentOnSite_baseIdealSubmodule (X := X.1) (hX := X.2) I)).map z := by
    refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun n => ?_))
    refine (cancel_epi (cokernel.π (idealPowerMultiple B _ hS X.1 X.2
      (C1573.baseIdealSubmodule X.1 X.2 I) (n.unop + 1) 𝒦.toSheafOfModules).ι)).1 ?_
    change _ ≫ idealPowerQuotientMapOfHom B _ hS X.1 X.2 _ (n.unop + 1) 𝒦.ι =
      _ ≫ idealPowerQuotientMapOfHom B _ hS X.1 X.2 _ (n.unop + 1) 0
    rw [π_comp_idealPowerQuotientMapOfHom, π_comp_idealPowerQuotientMapOfHom, hπ, zero_comp]
  -- the supports
  have := isFiniteTypeOnSite_of_isCoherentOnSite B _ hS X F.obj
  have := isFiniteTypeOnSite_of_isCoherentOnSite B _ hS X G.obj
  have hFcl := isClosed_supportOfSheaf_of_isFiniteTypeOnSite B _ hS X.1 X.2 F.obj
  have hGcl := isClosed_supportOfSheaf_of_isFiniteTypeOnSite B _ hS X.1 X.2 G.obj
  have hcl := hFcl.inter hGcl
  have hιz : ι = z := (bijective_completionFunctor_map_of_isProperOver X I f hlft F G hcl
    (isProperOver_of_isProper B _ hS X.2 _ f.hom hlft hf _ hcl)).1 hcomp
  have h : 𝒦.ι = 0 := congrArg (fun k => k.hom) hιz
  have hle := le_of_definingIdealSheaf_le B _ hS X ⟨⊤, isClosedSubspace_top B _ hS X⟩ C
    (fun U x hx => by
      have hx0 : x = 0 := congrArg (fun k => k.val.app U ⟨x, hx⟩) h
      rw [hx0]
      exact Submodule.zero_mem _)
  exact top_le_iff.1 hle

end Krull

end AlgebraicGeometry.Space

end
