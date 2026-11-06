module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.RepresentationStalkFunctoriality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkExactnessCriterion
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.EtaleFundamental.ChangeBasePoint
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ModuleSheafSideConditions
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicCompactSupportFunctoriality

/-!
# Short exact sequences of representations give short exact sequences of `ℱ_ρ`

The canonical equivalence of Tag 0DV5 (2) between finite locally constant abelian sheaves on a
connected scheme `X` and finite discrete `π₁(X, x̄)`-modules identifies the stalk at every
geometric point with the module (along a path), naturally.  Hence a sequence of finite
`π₁(X, x̄)`-modules which is exact on underlying groups goes to an exact sequence of abelian
sheaves (exactness is checked on geometric stalks, Tag 03PU).

## Main results

* `canonicalStalkIso_naturality`: the stalk of the image of a module map is the module map.
* `shortExact_canonicalFiniteLocallyConstantAbelianSheafEquivalence_inverse_map`: a short
  exact sequence of finite discrete `π₁(X, x̄)`-modules goes to a short exact sequence of
  abelian sheaves.
* `shortExact_padicLevelMap_representationLAdicSheafMap`: a short exact sequence of
  continuous `ℤ_ℓ`-representations gives a short exact sequence of ℓ-adic sheaves at every
  level.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.ConstantSheaf
  Stacks.GroupCohomology

universe u

attribute [local instance] discreteForget₂AddCommGrpCat

open scoped Stacks.DiscreteModuleTopology Matrix ZeroObject

namespace Stacks.EtaleCohomology

section Abelian

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)

/-- The stalk at `s̄` of the abelian sheaf attached to a finite `π₁(X, x̄)`-module `M` by the
canonical equivalence of Tag 0DV5 (2) is `M`, along a path `t` from `s̄` to `x̄`. -/
public def canonicalStalkIso {s : GeometricPoint X.1}
    (t : finiteEtaleFiberFunctor s ≅ finiteEtaleFiberFunctor x)
    (M : (ContinuousGAddCommGrp.isFinite.{u + 1, u + 1}
      (EtaleFundamentalGroup X.1 x)).FullSubcategory) :
    (abelianEtaleStalkFunctor.{u, u + 1} B X.1 X.2 s).obj
        ((canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x).inverse.obj M).obj ≅
      (ObjectProperty.ι _ ⋙ ContinuousGAddCommGrp.forget (EtaleFundamentalGroup X.1 x)).obj M :=
  (finiteLocallyConstantAbelianStalkIso B X t).app
      ((canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x).inverse.obj M) ≪≫
    (ObjectProperty.ι _ ⋙ ContinuousGAddCommGrp.forget (EtaleFundamentalGroup X.1 x)).mapIso
      ((canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x).counitIso.app M)

/-- `canonicalStalkIso` is natural in the module. -/
public theorem canonicalStalkIso_naturality {s : GeometricPoint X.1}
    (t : finiteEtaleFiberFunctor s ≅ finiteEtaleFiberFunctor x)
    {M N : (ContinuousGAddCommGrp.isFinite.{u + 1, u + 1}
      (EtaleFundamentalGroup X.1 x)).FullSubcategory}
    (φ : M ⟶ N) :
    (abelianEtaleStalkFunctor.{u, u + 1} B X.1 X.2 s).map
        ((canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x).inverse.map φ).hom ≫
      (canonicalStalkIso B X x t N).hom =
    (canonicalStalkIso B X x t M).hom ≫
      (ObjectProperty.ι _ ⋙ ContinuousGAddCommGrp.forget (EtaleFundamentalGroup X.1 x)).map φ := by
  have h2 := (finiteLocallyConstantAbelianStalkIso B X t).hom.naturality
    ((canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x).inverse.map φ)
  have h3 := (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x).counitIso.hom.naturality
    φ
  have h3' := congrArg (fun g => (ObjectProperty.ι _ ⋙
    ContinuousGAddCommGrp.forget (EtaleFundamentalGroup X.1 x)).map g) h3
  simp only [Functor.map_comp] at h3'
  simp only [canonicalStalkIso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) h2).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) h3').trans ?_
  simp only [Functor.id_map]
  rfl

/-- On elements: the stalk map of the image of `φ` is `φ`, under `canonicalStalkIso`. -/
public theorem canonicalStalkIso_hom_map_apply {s : GeometricPoint X.1}
    (t : finiteEtaleFiberFunctor s ≅ finiteEtaleFiberFunctor x)
    {M N : (ContinuousGAddCommGrp.isFinite.{u + 1, u + 1}
      (EtaleFundamentalGroup X.1 x)).FullSubcategory}
    (φ : M ⟶ N) (y) :
    (canonicalStalkIso B X x t N).hom ((abelianEtaleStalkFunctor.{u, u + 1} B X.1 X.2 s).map
        ((canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x).inverse.map φ).hom y) =
      (ObjectProperty.ι _ ⋙ ContinuousGAddCommGrp.forget (EtaleFundamentalGroup X.1 x)).map φ
        ((canonicalStalkIso B X x t M).hom y) :=
  ConcreteCategory.congr_hom (canonicalStalkIso_naturality B X x t φ) y

/-- An element of `M₂` hit by `φ` and corresponding to `b` under `canonicalStalkIso` lifts to
an element of the stalk of the sheaf of `M₁` mapping to `b`. -/
private theorem exists_abelianEtaleStalk_map_eq {s : GeometricPoint X.1}
    (t : finiteEtaleFiberFunctor s ≅ finiteEtaleFiberFunctor x)
    {M₁ M₂ : (ContinuousGAddCommGrp.isFinite.{u + 1, u + 1}
      (EtaleFundamentalGroup X.1 x)).FullSubcategory}
    (φ : M₁ ⟶ M₂) {b : (abelianEtaleStalkFunctor.{u, u + 1} B X.1 X.2 s).obj
      ((canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x).inverse.obj M₂).obj}
    {a : (ObjectProperty.ι _ ⋙ ContinuousGAddCommGrp.forget (EtaleFundamentalGroup X.1 x)).obj M₁}
    (ha : (ObjectProperty.ι _ ⋙ ContinuousGAddCommGrp.forget (EtaleFundamentalGroup X.1 x)).map φ
      a = (canonicalStalkIso B X x t M₂).hom b) :
    ∃ a', (abelianEtaleStalkFunctor.{u, u + 1} B X.1 X.2 s).map
        ((canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x).inverse.map φ).hom a' = b :=
  ⟨(canonicalStalkIso B X x t M₁).inv a,
    ConcreteCategory.injective_of_mono_of_preservesPullback (canonicalStalkIso B X x t M₂).hom
      (by rw [canonicalStalkIso_hom_map_apply, Iso.inv_hom_id_apply, ha])⟩

/-- **Exactness on underlying groups gives exactness on geometric stalks.** -/
public theorem exact_abelianEtaleStalk_map_of_exact {s : GeometricPoint X.1}
    {M₁ M₂ M₃ : (ContinuousGAddCommGrp.isFinite.{u + 1, u + 1}
      (EtaleFundamentalGroup X.1 x)).FullSubcategory}
    (φ : M₁ ⟶ M₂) (ψ : M₂ ⟶ M₃)
    (h : Function.Exact
      ((ObjectProperty.ι _ ⋙ ContinuousGAddCommGrp.forget (EtaleFundamentalGroup X.1 x)).map φ)
      ((ObjectProperty.ι _ ⋙ ContinuousGAddCommGrp.forget (EtaleFundamentalGroup X.1 x)).map ψ)) :
    Function.Exact ((abelianEtaleStalkFunctor.{u, u + 1} B X.1 X.2 s).map
        ((canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x).inverse.map φ).hom)
      ((abelianEtaleStalkFunctor.{u, u + 1} B X.1 X.2 s).map
        ((canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x).inverse.map ψ).hom) := by
  obtain ⟨t⟩ := nonempty_finiteEtaleFiberFunctorIso (x := s) (x' := x)
  intro y
  constructor
  · intro hy
    have e₂ := canonicalStalkIso_hom_map_apply B X x t ψ y
    rw [hy, map_zero] at e₂
    obtain ⟨a, ha⟩ := (h ((canonicalStalkIso B X x t M₂).hom y)).1 e₂.symm
    exact exists_abelianEtaleStalk_map_eq B X x t φ ha
  · rintro ⟨a, rfl⟩
    apply ConcreteCategory.injective_of_mono_of_preservesPullback (canonicalStalkIso B X x t M₃).hom
    rw [canonicalStalkIso_hom_map_apply, canonicalStalkIso_hom_map_apply, map_zero]
    exact (h _).2 ⟨_, rfl⟩

/-- Injectivity on underlying groups gives injectivity on geometric stalks. -/
public theorem injective_abelianEtaleStalk_map_of_injective {s : GeometricPoint X.1}
    {M₁ M₂ : (ContinuousGAddCommGrp.isFinite.{u + 1, u + 1}
      (EtaleFundamentalGroup X.1 x)).FullSubcategory}
    (φ : M₁ ⟶ M₂)
    (h : Function.Injective
      ((ObjectProperty.ι _ ⋙ ContinuousGAddCommGrp.forget (EtaleFundamentalGroup X.1 x)).map φ)) :
    Function.Injective ((abelianEtaleStalkFunctor.{u, u + 1} B X.1 X.2 s).map
        ((canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x).inverse.map φ).hom) := by
  obtain ⟨t⟩ := nonempty_finiteEtaleFiberFunctorIso (x := s) (x' := x)
  intro a b hab
  have ha := canonicalStalkIso_hom_map_apply B X x t φ a
  have hb := canonicalStalkIso_hom_map_apply B X x t φ b
  rw [hab, hb] at ha
  exact ConcreteCategory.injective_of_mono_of_preservesPullback (canonicalStalkIso B X x t M₁).hom
    (h ha).symm

/-- Surjectivity on underlying groups gives surjectivity on geometric stalks. -/
public theorem surjective_abelianEtaleStalk_map_of_surjective {s : GeometricPoint X.1}
    {M₁ M₂ : (ContinuousGAddCommGrp.isFinite.{u + 1, u + 1}
      (EtaleFundamentalGroup X.1 x)).FullSubcategory}
    (φ : M₁ ⟶ M₂)
    (h : Function.Surjective
      ((ObjectProperty.ι _ ⋙ ContinuousGAddCommGrp.forget (EtaleFundamentalGroup X.1 x)).map φ)) :
    Function.Surjective ((abelianEtaleStalkFunctor.{u, u + 1} B X.1 X.2 s).map
        ((canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x).inverse.map φ).hom) := by
  obtain ⟨t⟩ := nonempty_finiteEtaleFiberFunctorIso (x := s) (x' := x)
  intro b
  obtain ⟨a, ha⟩ := h ((canonicalStalkIso B X x t M₂).hom b)
  exact exists_abelianEtaleStalk_map_eq B X x t φ ha

/-- **A sequence of finite `π₁(X, x̄)`-modules, short exact on underlying groups, goes to a short
exact sequence of abelian sheaves** under the canonical equivalence of Tag 0DV5 (2): exactness,
injectivity and surjectivity are checked on geometric stalks (Tag 03PU), where they are those of
the modules. -/
public theorem shortExact_canonicalFiniteLocallyConstantAbelianSheafEquivalence_inverse_map
    {M₁ M₂ M₃ : (ContinuousGAddCommGrp.isFinite.{u + 1, u + 1}
      (EtaleFundamentalGroup X.1 x)).FullSubcategory}
    (φ : M₁ ⟶ M₂) (ψ : M₂ ⟶ M₃)
    (hw : ((canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x).inverse.map φ).hom ≫
      ((canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x).inverse.map ψ).hom = 0)
    (hinj : Function.Injective
      ((ObjectProperty.ι _ ⋙ ContinuousGAddCommGrp.forget (EtaleFundamentalGroup X.1 x)).map φ))
    (hsurj : Function.Surjective
      ((ObjectProperty.ι _ ⋙ ContinuousGAddCommGrp.forget (EtaleFundamentalGroup X.1 x)).map ψ))
    (hex : Function.Exact
      ((ObjectProperty.ι _ ⋙ ContinuousGAddCommGrp.forget (EtaleFundamentalGroup X.1 x)).map φ)
      ((ObjectProperty.ι _ ⋙ ContinuousGAddCommGrp.forget (EtaleFundamentalGroup X.1 x)).map ψ)) :
    (ShortComplex.mk _ _ hw).ShortExact := by
  set f := ((canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x).inverse.map φ).hom
  set g := ((canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x).inverse.map ψ).hom
  have hexact : (ShortComplex.mk _ _ hw).Exact :=
    (exact_iff_etaleStalk_exact.{u, u + 1} B X.1 X.2 _).2 fun s =>
      exact_abelianEtaleStalk_map_of_exact B X x φ ψ hex (s := s)
  have hmono : Mono f := by
    have h0 : (0 : (0 : Sheaf (SmallEtale.topology B X.1 X.2) AddCommGrpCat.{u + 1}) ⟶ _) ≫ f = 0 :=
      zero_comp
    refine (ShortComplex.exact_iff_mono (ShortComplex.mk _ _ h0) rfl).1 ?_
    refine (exact_iff_etaleStalk_exact.{u, u + 1} B X.1 X.2 _).2 fun s b => ?_
    have hinj' := injective_abelianEtaleStalk_map_of_injective B X x φ hinj (s := s)
    refine ⟨fun hb => ⟨0, by rw [hinj' (hb.trans (map_zero _).symm), map_zero]; rfl⟩, ?_⟩
    rintro ⟨a, rfl⟩
    show (abelianEtaleStalkFunctor.{u, u + 1} B X.1 X.2 s).map f
      ((abelianEtaleStalkFunctor.{u, u + 1} B X.1 X.2 s).map 0 a) = 0
    rw [Functor.map_zero]
    show (abelianEtaleStalkFunctor.{u, u + 1} B X.1 X.2 s).map f 0 = 0
    exact map_zero _
  have hepi : Epi g := by
    have h0 : g ≫ (0 : _ ⟶ (0 : Sheaf (SmallEtale.topology B X.1 X.2) AddCommGrpCat.{u + 1})) = 0 :=
      comp_zero
    refine (ShortComplex.exact_iff_epi (ShortComplex.mk _ _ h0) rfl).1 ?_
    refine (exact_iff_etaleStalk_exact.{u, u + 1} B X.1 X.2 _).2 fun s b => ?_
    have hsurj' := surjective_abelianEtaleStalk_map_of_surjective B X x ψ hsurj (s := s)
    refine ⟨fun _ => hsurj' b, fun _ => ?_⟩
    show (abelianEtaleStalkFunctor.{u, u + 1} B X.1 X.2 s).map 0 b = 0
    rw [Functor.map_zero]
    rfl
  exact { exact := hexact, mono_f := hmono, epi_g := hepi }

end Abelian

section Reflect

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (R : Type) [Ring R]

/-- `R`-modules have all limits at the carrier universe `u + 1`. -/
local instance hasLimitsOfSize_moduleCat_smallEtale :
    HasLimitsOfSize.{u + 1, u + 1} (ModuleCat.{u + 1} R) :=
  ModuleCat.hasLimitsOfSize.{u + 1, u + 1, u + 1, 0}

/-- Composing with the forgetful functor from `R`-modules to abelian groups sends sheaves on the
small étale site to sheaves. -/
local instance hasSheafCompose_forget₂_smallEtale :
    (SmallEtale.topology B X.1 X.2).HasSheafCompose
      (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}) :=
  Stacks.ModuleSheaf.hasSheafCompose_forget₂.{u + 1} _ _

/-- The forgetful functor from `R`-modules to abelian groups commutes with sheafification on
the small étale site. -/
local instance preservesSheafification_forget₂_smallEtale :
    (SmallEtale.topology B X.1 X.2).PreservesSheafification
      (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}) :=
  Stacks.ModuleSheaf.preservesSheafification_forget₂.{u + 1} _ _

/-- The abelian sheaf underlying a sheaf of `R`-modules on the small étale site preserves finite
limits, limits of sheaves being computed sectionwise. -/
public instance preservesFiniteLimits_sheafCompose_forget₂_smallEtale :
    PreservesFiniteLimits (sheafCompose (SmallEtale.topology B X.1 X.2)
      (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1})) := by
  constructor
  intro I _ _
  have : PreservesLimitsOfShape I (sheafCompose (SmallEtale.topology B X.1 X.2)
      (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}) ⋙
        sheafToPresheaf _ AddCommGrpCat.{u + 1}) :=
    inferInstanceAs (PreservesLimitsOfShape I
      (sheafToPresheaf _ _ ⋙ (Functor.whiskeringRight _ _ _).obj
        (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1})))
  exact preservesLimitsOfShape_of_reflects_of_preserves _ (sheafToPresheaf _ _)

/-- It preserves finite colimits: it commutes with sheafification and the forgetful functor of
modules preserves colimits. -/
public instance preservesFiniteColimits_sheafCompose_forget₂_smallEtale :
    PreservesFiniteColimits (sheafCompose (SmallEtale.topology B X.1 X.2)
      (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1})) := by
  constructor
  intro I _ _
  exact Sheaf.preservesColimitsOfShape_sheafCompose _ _

/-- **Short exactness of sheaves of `R`-modules is detected on the underlying abelian sheaves.** -/
public theorem shortExact_of_shortExact_map_sheafCompose_forget₂
    (S : ShortComplex (Sheaf (SmallEtale.topology B X.1 X.2) (ModuleCat.{u + 1} R)))
    (h : (S.map (sheafCompose (SmallEtale.topology B X.1 X.2)
      (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}))).ShortExact) : S.ShortExact := by
  let U := sheafCompose (SmallEtale.topology B X.1 X.2)
    (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1})
  have : U.PreservesHomology :=
    { preservesKernels := fun _ => inferInstance
      preservesCokernels := fun _ => inferInstance }
  have : Mono S.f := U.mono_of_mono_map h.mono_f
  have : Epi S.g := U.epi_of_epi_map h.epi_g
  exact { exact := (ShortComplex.exact_map_iff_of_faithful S U).1 h.exact }

end Reflect

section LAdic

open AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  {ℓ : ℕ} [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [IsNoetherian X.1]

/-- **A short exact sequence of continuous `ℤ_ℓ`-representations gives a short exact sequence of
ℓ-adic sheaves at every level.**  For intertwiners `A : ρ₁ → ρ₂`, `C : ρ₂ → ρ₃` whose reductions
modulo every `ℓ ^ k` form short exact sequences
`0 → (ℤ/ℓ^k)^{r₁} → (ℤ/ℓ^k)^{r₂} → (ℤ/ℓ^k)^{r₃} → 0`, the level-`n` components of `ℱ_A` and
`ℱ_C`, as sheaves of `ℤ_ℓ`-modules, form a short exact sequence: on underlying abelian sheaves
they are the images of the module maps under the canonical equivalence of Tag 0DV5 (2). -/
public theorem shortExact_padicLevelMap_representationLAdicSheafMap {r₁ r₂ r₃ : ℕ}
    {ρ₁ : EtaleFundamentalGroup X.1 x →* GL (Fin r₁) ℤ_[ℓ]} (hρ₁ : Continuous ρ₁)
    {ρ₂ : EtaleFundamentalGroup X.1 x →* GL (Fin r₂) ℤ_[ℓ]} (hρ₂ : Continuous ρ₂)
    {ρ₃ : EtaleFundamentalGroup X.1 x →* GL (Fin r₃) ℤ_[ℓ]} (hρ₃ : Continuous ρ₃)
    (A : Matrix (Fin r₂) (Fin r₁) ℤ_[ℓ]) (hA : ∀ g, A * (ρ₁ g).val = (ρ₂ g).val * A)
    (C : Matrix (Fin r₃) (Fin r₂) ℤ_[ℓ]) (hC : ∀ g, C * (ρ₂ g).val = (ρ₃ g).val * C)
    (hinj : ∀ k, Function.Injective (A.map (PadicInt.toZModPow k)).mulVec)
    (hsurj : ∀ k, Function.Surjective (C.map (PadicInt.toZModPow k)).mulVec)
    (hex : ∀ k, Function.Exact (A.map (PadicInt.toZModPow k)).mulVec
      (C.map (PadicInt.toZModPow k)).mulVec) (n : ℕ)
    (hw : LAdicSheaf.padicLevelMap (representationLAdicSheafMap B X x
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) hρ₁ hρ₂ A hA) n ≫
      LAdicSheaf.padicLevelMap (representationLAdicSheafMap B X x
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) hρ₂ hρ₃ C hC) n = 0) :
    (ShortComplex.mk _ _ hw).ShortExact := by
  apply shortExact_of_shortExact_map_sheafCompose_forget₂ B X ℤ_[ℓ]
  have hw' := congrArg (sheafCompose (SmallEtale.topology B X.1 X.2)
    (forget₂ (ModuleCat.{u + 1} ℤ_[ℓ]) AddCommGrpCat.{u + 1})).map hw
  rw [Functor.map_comp, Functor.map_zero] at hw'
  exact shortExact_canonicalFiniteLocallyConstantAbelianSheafEquivalence_inverse_map B X x
    (levelAbelianMap hρ₁ hρ₂ A hA (n + 1)) (levelAbelianMap hρ₂ hρ₃ C hC (n + 1)) hw'
    (fun a b h => ULift.ext (hinj (n + 1) (congrArg ULift.down h)))
    (fun c => by
      obtain ⟨b, hb⟩ := hsurj (n + 1) c.down
      exact ⟨ULift.up b, ULift.ext hb⟩)
    (fun b => by
      show ULift.up _ = (0 : ULift _) ↔ _
      refine ⟨fun h => ?_, ?_⟩
      · obtain ⟨a, ha⟩ := (hex (n + 1) b.down).1 (congrArg ULift.down h)
        exact ⟨ULift.up a, ULift.ext ha⟩
      · rintro ⟨a, rfl⟩
        exact ULift.ext ((hex (n + 1) _).2 ⟨a.down, rfl⟩))

end LAdic

end Stacks.EtaleCohomology

end
