module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ModuleShriekFiniteGeneration
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.ConstructibleFlatShriek
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.BoundedAboveShriekComplex
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.GlobalStratification
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantCoefficients
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.EtaleModulesCtf
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedAboveResolution
public import StacksFrontier.CategoryTheory.Sites.LocallyBijectiveUniverse
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Covering epimorphisms onto constructible sheaves of modules over a noncommutative ring

Let `X` be a quasi-compact and quasi-separated scheme of a big étale site and let `Λ` be a
(left) Noetherian ring, **not necessarily commutative**. Every epimorphism `p : Z ⟶ H` of sheaves
of `Λ`-modules on `X_étale` onto a constructible sheaf `H` is refined by a finite direct sum of
sheaves `j_{U!}\underline{\Lambda}_U` with `U` a quasi-compact quasi-separated étale object: there
is a map `f` from such a sum into `Z` with `f ≫ p` an epimorphism, and the sum is a constructible
flat sheaf of `Λ`-modules.

This is the generation step of [Stacks, Tag 095N] — [Stacks, Tag 093B] part (2) followed by the
finite generation step of [Stacks, Tag 095P] — together with the flat refinement of
[Stacks, Tag 03S8], for the possibly noncommutative finite coefficient rings of the trace formula
(Tag 03SZ). The library states these steps for a commutative ring; none of their proofs uses
commutativity, and they are given here for an arbitrary ring, with the Noetherian hypothesis only
where finite generation of stalks is used.

## Main results

* `AlgebraicGeometry.exists_epi_sigma_moduleShriekConstant_qcqs_of_ring` — Tag 093B part (2).
* `AlgebraicGeometry.isConstructibleFlatModuleSheaf_moduleShriekConstant_of_ring` — the flat
  refinement of Tag 03S8.
* `AlgebraicGeometry.exists_finset_epi_sigma_desc_of_isConstructibleModuleSheaf_of_ring` — the
  finite generation step of Tag 095P.
* `AlgebraicGeometry.coversEpis_isConstructibleFlatModuleSheaf` — **finite sums of generators
  cover epimorphisms onto constructible sheaves**, in the form consumed by
  `Stacks.Homology.BoundedAboveResolution.exists_quasiIso_isStrictlyLE_of_coversEpis`.

## References

* [Stacks Project, Tag 093B](https://stacks.math.columbia.edu/tag/093B)
* [Stacks Project, Tag 095N](https://stacks.math.columbia.edu/tag/095N)
* [Stacks Project, Tag 095P](https://stacks.math.columbia.edu/tag/095P)
* [Stacks Project, Tag 03S8](https://stacks.math.columbia.edu/tag/03S8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CoproductsFromFiniteFiltered

universe u r

attribute [local instance 2000] Sheaf.instHasColimitsOfShape Sheaf.instHasFiniteCoproducts
attribute [local implicit_reducible] CoproductsFromFiniteFiltered.liftToFinsetObj
  CoproductsFromFiniteFiltered.finiteSubcoproductsCocone

namespace AlgebraicGeometry

section Instances

variable (B : BigEtaleSite.{u}) (Λ : Type r) [Ring Λ]

/-- Sheafification of presheaves of `Λ`-modules on the small étale site, at the coefficient
universe `max (u + 1) r`, for an arbitrary ring. -/
theorem smallEtaleHasSheafifyModuleMax_of_ring (X : B.Scheme) :
    HasSheafify (SmallEtale.topology B X.1 X.property) (ModuleCat.{max (u + 1) r} Λ) :=
  SmallEtale.hasSheafify_moduleCat.{u, r, r} B X Λ

/-- Sheaves of `Λ`-modules on the small étale site have colimits of size `max (u + 1) r`, for an
arbitrary ring. -/
theorem smallEtaleHasColimitsOfSizeModuleMax_of_ring (X : B.Scheme) :
    HasColimitsOfSize.{max (u + 1) r, max (u + 1) r}
      (Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{max (u + 1) r} Λ)) :=
  let := smallEtaleHasSheafifyModuleMax_of_ring B Λ X
  let : HasColimitsOfSize.{max (u + 1) r, max (u + 1) r} (ModuleCat.{max (u + 1) r} Λ) :=
    inferInstance
  CategoryTheory.Sheaf.instHasColimitsOfSize

/-- The forgetful functor of `Λ`-modules preserves filtered colimits at the coefficient universe
`max (u + 1) r`, for an arbitrary ring. -/
theorem preservesFilteredColimits_forget_moduleCatMax_of_ring (Λ : Type r) [Ring Λ] :
    PreservesFilteredColimits (forget (ModuleCat.{max (u + 1) r} Λ)) :=
  let : PreservesColimitsOfSize.{max (u + 1) r, max (u + 1) r}
      (forget₂ (ModuleCat.{max (u + 1) r} Λ) AddCommGrpCat.{max (u + 1) r}) :=
    ModuleCat.forget₂PreservesColimitsOfSize.{max (u + 1) r, r,
      max (u + 1) r, max (u + 1) r} Λ
  comp_preservesFilteredColimits
    (forget₂ (ModuleCat.{max (u + 1) r} Λ) AddCommGrpCat.{max (u + 1) r})
    (forget AddCommGrpCat.{max (u + 1) r})

/-- The forgetful functor of `Λ`-modules preserves the size-`u` filtered colimits defining the
étale stalks, for an arbitrary ring. -/
theorem preservesFilteredColimitsOfSize_forget_moduleCatMax_of_ring (Λ : Type r) [Ring Λ] :
    PreservesFilteredColimitsOfSize.{u, u} (forget (ModuleCat.{max (u + 1) r} Λ)) :=
  let := preservesFilteredColimits_forget_moduleCatMax_of_ring.{u, r} Λ
  preservesFilteredColimitsOfSize_of_univLE.{max (u + 1) r, max (u + 1) r, u, u}
    (forget (ModuleCat.{max (u + 1) r} Λ))

end Instances

section GeneralRing

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type r) [Ring Λ]

attribute [local instance] smallEtaleHasSheafifyModuleMax_of_ring
  smallEtaleHasColimitsOfSizeModuleMax_of_ring
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring
  SmallEtale.hasWeakSheafify_over_moduleCat_ring

/-- **`j_{U!}\underline{\Lambda}_U` corepresents sections over `U`**, for an arbitrary ring. This
is the proof of `AlgebraicGeometry.moduleShriekConstantCoyonedaIso`, which uses no
commutativity. -/
def moduleShriekConstantCoyonedaIsoOfRing (U : SmallEtale B X.1 X.property) :
    coyoneda.obj (op (moduleShriekConstant.{u, r, r} B X Λ U)) ≅
      (sheafSections (SmallEtale.topology B X.1 X.property)
          (ModuleCat.{max (u + 1) r} Λ)).obj (op U) ⋙
        forget (ModuleCat.{max (u + 1) r} Λ) := by
  letI := SmallEtale.hasSheafify_moduleCat.{u, r, r} B X Λ
  letI := SmallEtale.hasSheafify_moduleCat.{u, r, r} B U.obj.left Λ
  refine (Sheaf.coyonedaSheafPullbackConstantSheafIso.{u, u + 1, u, u + 1, r, r}
    (smallEtalePostcompose B X.1 X.property U)
    (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
    (SmallEtale.topology B X.1 X.property) Λ
    (SmallEtale.finalIsTerminal B U.obj.left.1 U.obj.left.property)
    (ModuleCat.of Λ (ULift.{max (u + 1) r} Λ))).trans
      ((Functor.isoWhiskerLeft _
        (ModuleCat.coyonedaULiftSelfIso.{r, max (u + 1) r} Λ)).trans ?_)
  exact Functor.isoWhiskerRight
    (((sheafSections (SmallEtale.topology B X.1 X.property)
      (ModuleCat.{max (u + 1) r} Λ)).mapIso
        (smallEtalePostcomposeFinalIso B X U).op).symm)
    (forget (ModuleCat.{max (u + 1) r} Λ))

/-- **Stacks 093B part (2) for sheaves of modules over an arbitrary ring.** Every sheaf of
`Λ`-modules on the small étale site of `X` is a quotient of a direct sum of sheaves
`j_{U!}\underline{\Lambda}_U` at quasi-compact quasi-separated étale objects `U`. -/
theorem exists_epi_sigma_moduleShriekConstant_qcqs_of_ring (B : BigEtaleSite.{u}) (X : B.Scheme)
    (Λ : Type r) [Ring Λ]
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{max (u + 1) r} Λ)) :
    ∃ (A : Type max (u + 1) r) (U : A → SmallEtale B X.1 X.property),
      (∀ a, IsQCQSEtaleObject B X (U a)) ∧
        ∃ p : (∐ fun a => moduleShriekConstant.{u, r, r} B X Λ (U a)) ⟶ F, Epi p :=
  Sheaf.exists_epi_sigma_of_coyonedaSections.{u, u + 1, r, r}
    (SmallEtale.quasiCompactObjectsSituation B X)
    (SmallEtale.hasEnoughObjects_quasiCompactObjectsSituation B X) Λ
    (fun U => moduleShriekConstant.{u, r, r} B X Λ U)
    (fun U => moduleShriekConstantCoyonedaIsoOfRing B X Λ U) F

/-- **The extension by zero of the constant free rank-one module sheaf is the copower module
sheaf on `h_U^#`**, for an arbitrary ring. This is the proof of
`AlgebraicGeometry.moduleShriekConstantIsoCopower`, which uses no commutativity. -/
def moduleShriekConstantIsoCopowerOfRing (U : SmallEtale B X.1 X.property) :
    moduleShriekConstant.{u, r, r} B X Λ U ≅
      (Sheaf.composeAndSheafify (SmallEtale.topology B X.1 X.property)
          (ModuleCat.copower (ModuleCat.of Λ (ULift.{max (u + 1) r} Λ)))).obj
        ((Sheaf.sheafifiedUliftYoneda.{r} (SmallEtale.topology B X.1 X.property)).obj U) := by
  letI := SmallEtale.hasSheafify_moduleCat.{u, r, r} B X Λ
  letI := SmallEtale.hasSheafify_moduleCat.{u, r, r} B U.obj.left Λ
  exact (Sheaf.sheafPullbackConstantSheafIsoComposeAndSheafifyCopowerUlift.{r, u, u + 1, u, u + 1}
      (smallEtalePostcompose B X.1 X.property U) _ _ Λ
      (ModuleCat.of Λ (ULift.{max (u + 1) r} Λ))
      (SmallEtale.finalIsTerminal B U.obj.left.1 U.obj.left.property)).trans
    ((Sheaf.composeAndSheafify (SmallEtale.topology B X.1 X.property)
      (ModuleCat.copower (ModuleCat.of Λ (ULift.{max (u + 1) r} Λ)))).mapIso
        ((Sheaf.sheafifiedUliftYoneda.{r} (SmallEtale.topology B X.1 X.property)).mapIso
          (smallEtalePostcomposeFinalIso B X U)))

attribute [local instance] isRightAdjoint_sheafPushforwardContinuous_type_uliftSmallEtale in
/-- **Flat constructibility transfers across the copower module sheaf functor**, for an arbitrary
ring: the copower module sheaf by a finite free module on a constructible sheaf of sets is flat
constructible. The proof is that of
`AlgebraicGeometry.isConstructibleFlatModuleSheaf_composeAndSheafify_copower`. -/
theorem isConstructibleFlatModuleSheaf_composeAndSheafify_copower_of_ring (B : BigEtaleSite.{u})
    (X : B.Scheme) (Λ : Type r) [Ring Λ]
    (M : ModuleCat.{max (u + 1) r} Λ) [Module.Finite Λ M] [Module.Free Λ M]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (Type max (u + 1) r))
    (hF : IsConstructibleFiniteSheaf B X F) :
    IsConstructibleFlatModuleSheaf B X Λ
      ((Sheaf.composeAndSheafify (SmallEtale.topology B X.obj X.property)
        (ModuleCat.copower M)).obj F) := by
  intro U
  obtain ⟨s, hs⟩ := hF U
  refine ⟨s, fun i ↦ ?_⟩
  refine Stacks.ConstantSheaf.isFiniteProjectiveLocallyConstant_congr Λ _
    ((Sheaf.composeAndSheafifyModuleCopowerSheafPullbackIso
      (SmallEtale.topology B X.obj X.property) M
      (SmallEtale.topology B (s.piece i).obj (s.piece i).property)
      (smallEtaleBaseChange B (s.inclusion i))).app F).symm ?_
  have : EssentiallySmall.{max (u + 1) r} (SmallEtale B (s.piece i).obj (s.piece i).property) :=
    essentiallySmall_lift.{max (u + 1) r, u, u + 1, u} _
  have hV : ∀ V : SmallEtale B (s.piece i).obj (s.piece i).property,
      HasWeakSheafify ((SmallEtale.topology B (s.piece i).obj (s.piece i).property).over V)
        (Type (max (u + 1) r)) := fun V ↦
    have : HasSheafify ((SmallEtale.topology B (s.piece i).obj (s.piece i).property).over V)
        (Type (max (u + 1) r)) := hasSheafifyEssentiallySmallSite _ _
    inferInstance
  exact Stacks.ConstantSheaf.isFiniteProjectiveLocallyConstant_composeAndSheafify_copower _ Λ M _
    (hs i)

/-- **The flat refinement of Stacks 03S8 for sheaves of modules over an arbitrary ring.** For a
quasi-compact quasi-separated étale object `U` of a quasi-compact quasi-separated scheme `X`, the
sheaf `j_{U!}\underline{\Lambda}_U` is a flat constructible sheaf of `Λ`-modules. The proof is
that of `AlgebraicGeometry.isConstructibleFlatModuleSheaf_moduleShriekConstant`. -/
theorem isConstructibleFlatModuleSheaf_moduleShriekConstant_of_ring (B : BigEtaleSite.{u})
    (X : B.Scheme) (Λ : Type r) [Ring Λ]
    [CompactSpace X.obj] [QuasiSeparatedSpace X.obj] (U : SmallEtale B X.obj X.property)
    [CompactSpace U.obj.left.obj] [QuasiSeparatedSpace U.obj.left.obj] :
    IsConstructibleFlatModuleSheaf B X Λ (moduleShriekConstant.{u, r, r} B X Λ U) := by
  intro V
  obtain ⟨s, hs⟩ := isConstructibleFlatModuleSheaf_composeAndSheafify_copower_of_ring B X Λ
    (ModuleCat.of Λ (ULift.{max (u + 1) r} Λ)) _
    (isConstructibleFiniteSheaf_sheafifiedUliftYoneda_of_qcqs.{r} B X U) V
  refine ⟨s, fun i ↦ ?_⟩
  exact Stacks.ConstantSheaf.isFiniteProjectiveLocallyConstant_congr Λ _
    (((smallEtaleBaseChange B (s.inclusion i)).sheafPullback (ModuleCat.{max (u + 1) r} Λ)
      (SmallEtale.topology B X.obj X.property)
      (SmallEtale.topology B (s.piece i).obj (s.piece i).property)).mapIso
        (moduleShriekConstantIsoCopowerOfRing B X Λ U).symm) (hs i)

end GeneralRing

section Stratification

universe w

/-- **Stacks 095E for sheaves of modules over an arbitrary ring, (1) ⟹ (3).** On a
quasi-compact quasi-separated scheme a constructible sheaf of `R`-modules admits one finite
constructible stratification of the whole scheme on whose strata it is locally constant of finite
type. -/
@[sga "4 IX 2.4" "(i)"]
theorem exists_stratification_top_of_isConstructibleModuleSheaf_of_ring (B : BigEtaleSite.{u})
    (X : B.Scheme) [CompactSpace X.obj] [QuasiSeparatedSpace X.obj] (R : Type r) [Ring R]
    [∀ (S T : B.Scheme) (f : T ⟶ S),
      ((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{w} R)
        (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
    [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
      HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) (ModuleCat.{w} R)]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} R))
    (hF : IsConstructibleModuleSheaf B X R F) :
    ∃ s : ConstructibleStratification B X ⊤,
      ∀ i, Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant R
        (SmallEtale.topology B (s.piece i).obj (s.piece i).property)
        (((smallEtaleBaseChange B (s.inclusion i)).sheafPullback (ModuleCat.{w} R)
          (SmallEtale.topology B X.obj X.property)
          (SmallEtale.topology B (s.piece i).obj (s.piece i).property)).obj F) :=
  exists_stratification_top_of_isStratifiedSheaf B X _
    (fun T _ _ e h => Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_congr
      (SmallEtale.topology B T.obj T.property) R e h)
    (fun _ _ q G h => isFiniteTypeLocallyConstant_smallEtaleSheafPullback B R q G h) F hF

/-- A sheaf of modules which is locally constant with finitely generated values is locally
constant. -/
private theorem isLocallyConstant_of_isFiniteTypeLocallyConstant_ring {C : Type*} [Category C]
    (J : GrothendieckTopology C) (R : Type r) [Ring R]
    [∀ V : C, HasWeakSheafify (J.over V) (ModuleCat.{w} R)]
    (F : Sheaf J (ModuleCat.{w} R))
    (hF : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant R J F) :
    Stacks.ConstantSheaf.IsLocallyConstant J F := by
  refine ⟨fun U => ?_⟩
  obtain ⟨I, V, f, hf, hdata⟩ := hF U
  refine ⟨I, V, f, hf, fun i => ?_⟩
  obtain ⟨E, -, hiso⟩ := hdata i
  exact ⟨⟨E, hiso⟩⟩

/-- **The locus of a stalkwise property of a constructible sheaf of modules is constructible**,
over an arbitrary ring. Let `F` be a constructible sheaf of `R`-modules on a quasi-compact
quasi-separated scheme `X` and `P` a property of `R`-modules invariant under isomorphism. The set
of points of `X` over which some geometric stalk of `F` has `P` is constructible: on the strata
of a global constructible stratification (Tag 095E) `F` is locally constant, and the locus of a
property of the stalks of a locally constant sheaf is open and closed in each stratum. -/
theorem isConstructible_setOf_exists_geometricPoint_etaleStalk_of_ring (B : BigEtaleSite.{u})
    (X : B.Scheme) [CompactSpace X.obj] [QuasiSeparatedSpace X.obj] (R : Type r) [Ring R]
    [UnivLE.{u, w}]
    [PreservesFilteredColimitsOfSize.{max u w, max u w} (forget (ModuleCat.{max u w} R))]
    [∀ (Z : B.Scheme) (V : SmallEtale B Z.obj Z.property),
      HasWeakSheafify ((SmallEtale.topology B Z.obj Z.property).over V) (ModuleCat.{max u w} R)]
    [∀ (Z : B.Scheme) (V : SmallEtale B Z.obj Z.property),
      ((SmallEtale.topology B Z.obj Z.property).over V).WEqualsLocallyBijective
        (ModuleCat.{max u w} R)]
    [∀ (Y Z : B.Scheme) (f : Z ⟶ Y),
      ((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{max u w} R)
        (SmallEtale.topology B Y.obj Y.property)
        (SmallEtale.topology B Z.obj Z.property)).IsRightAdjoint]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max u w} R))
    (hF : IsConstructibleModuleSheaf B X R F) (P : ModuleCat.{max u w} R → Prop)
    (hP : ∀ {E E' : ModuleCat.{max u w} R}, (E ≅ E') → (P E ↔ P E')) :
    Topology.IsConstructible {x : X.obj | ∃ t : GeometricPoint X.obj, t.LiesOver x ∧
      P (etaleStalk B X.obj X.property t F.obj)} := by
  obtain ⟨s, hs⟩ := exists_stratification_top_of_isConstructibleModuleSheaf_of_ring B X R F hF
  exact isConstructible_setOf_exists_geometricPoint_property_etaleStalk B X F
    ⟨s, fun k => isLocallyConstant_of_isFiniteTypeLocallyConstant_ring _ R _ (hs k)⟩ P hP

/-- **Stacks 09YS, part (3), over an arbitrary ring.** On a quasi-compact quasi-separated scheme
the support of a constructible sheaf of `R`-modules is constructible. The proof is that of
`AlgebraicGeometry.isConstructible_support_moduleSheaf`, which uses no commutativity. -/
theorem isConstructible_support_moduleSheaf_of_ring (B : BigEtaleSite.{u}) (X : B.Scheme)
    [CompactSpace X.obj] [QuasiSeparatedSpace X.obj] (R : Type r) [Ring R] [UnivLE.{u, w}]
    [PreservesFilteredColimitsOfSize.{max u w, max u w} (forget (ModuleCat.{max u w} R))]
    [∀ (Z : B.Scheme) (V : SmallEtale B Z.obj Z.property),
      HasWeakSheafify ((SmallEtale.topology B Z.obj Z.property).over V) (ModuleCat.{max u w} R)]
    [∀ (Z : B.Scheme) (V : SmallEtale B Z.obj Z.property),
      ((SmallEtale.topology B Z.obj Z.property).over V).WEqualsLocallyBijective
        (ModuleCat.{max u w} R)]
    [∀ (Y Z : B.Scheme) (f : Z ⟶ Y),
      ((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{max u w} R)
        (SmallEtale.topology B Y.obj Y.property)
        (SmallEtale.topology B Z.obj Z.property)).IsRightAdjoint]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max u w} R))
    (hF : IsConstructibleModuleSheaf B X R F) :
    Topology.IsConstructible {x : X.obj | ∃ t : GeometricPoint X.obj, t.LiesOver x ∧
      ¬ IsZero (etaleStalk B X.obj X.property t F.obj)} :=
  isConstructible_setOf_exists_geometricPoint_etaleStalk_of_ring B X R F hF
    (fun E => ¬ IsZero E) fun e => not_congr e.isZero_iff

end Stratification

section FiniteGeneration

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type r) [Ring Λ]

attribute [local instance] smallEtaleHasSheafifyModuleMax_of_ring
  smallEtaleHasColimitsOfSizeModuleMax_of_ring
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring
  SmallEtale.hasWeakSheafify_over_moduleCat_ring

private theorem wEqualsLocallyBijectiveModuleMaxRing (B : BigEtaleSite.{u}) (Λ : Type r) [Ring Λ]
    (T : B.Scheme)
    (V : SmallEtale B T.obj T.property) :
    ((SmallEtale.topology B T.obj T.property).over V).WEqualsLocallyBijective
      (ModuleCat.{max (u + 1) r} Λ) :=
  Stacks.ConstantSheaf.wEqualsLocallyBijective_moduleCat.{u, u + 1, r, r}
    ((SmallEtale.topology B T.obj T.property).over V) Λ

attribute [local instance 2000] wEqualsLocallyBijectiveModuleMaxRing

private theorem hasProductsModuleMaxRing (Λ : Type r) [Ring Λ] :
    HasProducts.{u} (ModuleCat.{max (u + 1) r} Λ) :=
  fun _ => ModuleCat.hasLimitsOfShape

private theorem hasLimitsOfSizeModuleMaxRing (Λ : Type r) [Ring Λ] :
    HasLimitsOfSize.{u, u} (ModuleCat.{max (u + 1) r} Λ) :=
  ModuleCat.hasLimitsOfSize.{u, u, max (u + 1) r, r}

attribute [local instance] hasProductsModuleMaxRing hasLimitsOfSizeModuleMaxRing

/-- The stalk at a geometric point, as the fibre functor of the point of the small étale site. -/
private abbrev moduleStalkRing (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type r) [Ring Λ]
    (t : GeometricPoint X.1) :
    Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{max (u + 1) r} Λ) ⥤
      ModuleCat.{max (u + 1) r} Λ :=
  (geometricPointSitePoint B X.1 X.property t).sheafFiber (A := ModuleCat.{max (u + 1) r} Λ)

private theorem preservesColimitsOfSize_moduleStalkRing (t : GeometricPoint X.1) :
    PreservesColimitsOfSize.{u + 1, u + 1} (moduleStalkRing B X Λ t) :=
  ((geometricPointSitePoint B X.1 X.property t).skyscraperSheafAdjunction
    (A := ModuleCat.{max (u + 1) r} Λ)).leftAdjoint_preservesColimits

private theorem isLeftAdjoint_moduleStalkRing (t : GeometricPoint X.1) :
    (moduleStalkRing B X Λ t).IsLeftAdjoint :=
  ((geometricPointSitePoint B X.1 X.property t).skyscraperSheafAdjunction
    (A := ModuleCat.{max (u + 1) r} Λ)).isLeftAdjoint

private theorem isZero_etaleStalk_cokernel_iff_ring
    {F F' : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{max (u + 1) r} Λ)}
    (f : F' ⟶ F) (t : GeometricPoint X.1) :
    IsZero (etaleStalk B X.1 X.property t (cokernel f).obj) ↔
      Epi ((moduleStalkRing B X Λ t).map f) := by
  have := isLeftAdjoint_moduleStalkRing B X Λ t
  have e : (moduleStalkRing B X Λ t).obj (cokernel f) ≅
      cokernel ((moduleStalkRing B X Λ t).map f) :=
    PreservesCokernel.iso _ _
  rw [Preadditive.epi_iff_isZero_cokernel]
  exact ⟨fun h => h.of_iso e.symm, fun h => h.of_iso e⟩

private theorem range_moduleStalkRing_map_sigma_desc_le
    {F : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{max (u + 1) r} Λ)}
    {A : Type max (u + 1) r}
    (M : A → Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{max (u + 1) r} Λ))
    (Ψ : (∐ M) ⟶ F) (t : GeometricPoint X.1) {s s' : Finset (Discrete A)} (h : s ≤ s') :
    LinearMap.range ((moduleStalkRing B X Λ t).map
        ((Sigma.desc fun a : {a // a ∈ s} => Sigma.ι M a.1.as) ≫ Ψ)).hom ≤
      LinearMap.range ((moduleStalkRing B X Λ t).map
        ((Sigma.desc fun a : {a // a ∈ s'} => Sigma.ι M a.1.as) ≫ Ψ)).hom := by
  have hw : ((Sigma.desc fun a : {a // a ∈ s} => Sigma.ι M a.1.as) ≫ Ψ) =
      (Sigma.desc fun a : {a // a ∈ s} =>
          Sigma.ι (fun a : {a // a ∈ s'} => M a.1.as) ⟨a.1, h a.2⟩) ≫
        ((Sigma.desc fun a : {a // a ∈ s'} => Sigma.ι M a.1.as) ≫ Ψ) := by
    rw [← Category.assoc]
    congr 1
    apply Sigma.hom_ext
    intro a
    simp
  rw [hw, Functor.map_comp]
  exact LinearMap.range_comp_le_range _ _

variable [IsNoetherianRing Λ]

omit [IsNoetherianRing Λ] in
/-- The geometric stalks of a constructible sheaf of `Λ`-modules are finitely generated, for an
arbitrary Noetherian ring: Tag 03TR through the stratumwise description. -/
private theorem isFG_moduleStalkRing_of_isConstructibleModuleSheaf
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{max (u + 1) r} Λ))
    (hF : IsConstructibleModuleSheaf B X Λ F) (t : GeometricPoint X.1) :
    ModuleCat.isFG Λ ((moduleStalkRing B X Λ t).obj F) :=
  stalk_prop_of_isStratifiedLocallyConstantWith B X Λ (ModuleCat.isFG Λ)
    (fun {E E'} e hE => by
      rw [ModuleCat.isFG_iff] at hE ⊢
      exact Module.Finite.equiv e.toLinearEquiv)
    (fun E hE => by
      rw [ModuleCat.isFG_iff]
      exact Module.Finite.of_finite)
    F hF t

omit [IsNoetherianRing Λ] in
/-- A finite subsum already surjects onto a stalk which is finitely generated. -/
private theorem exists_finset_epi_moduleStalkRing_map_sigma
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{max (u + 1) r} Λ))
    {A : Type max (u + 1) r}
    (G : A → Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{max (u + 1) r} Λ))
    (Ψ : (∐ G) ⟶ F) [Epi Ψ] (t : GeometricPoint X.1)
    (hfg : ModuleCat.isFG Λ ((moduleStalkRing B X Λ t).obj F)) :
    ∃ s : Finset (Discrete A), Epi ((moduleStalkRing B X Λ t).map
      ((Sigma.desc fun a : {a // a ∈ s} => Sigma.ι G a.1.as) ≫ Ψ)) := by
  classical
  have := preservesFilteredColimits_forget_moduleCatMax_of_ring.{u, r} Λ
  have hpres := preservesColimitsOfSize_moduleStalkRing B X Λ t
  have hcolim : IsColimit ((moduleStalkRing B X Λ t).mapCocone (finiteSubcoproductsCocone G)) :=
    isColimitOfPreserves (moduleStalkRing B X Λ t) (isColimitFiniteSubproductsCocone G)
  have hsurjΨ : Function.Surjective ((moduleStalkRing B X Λ t).map Ψ) :=
    (ModuleCat.epi_iff_surjective _).1 inferInstance
  rw [ModuleCat.isFG_iff] at hfg
  obtain ⟨T, hT⟩ := Module.finite_def.1 hfg
  have hmem : ∀ y : ToType ((moduleStalkRing B X Λ t).obj F), ∃ s : Finset (Discrete A),
      y ∈ LinearMap.range ((moduleStalkRing B X Λ t).map
        ((Sigma.desc fun a : {a // a ∈ s} => Sigma.ι G a.1.as) ≫ Ψ)).hom := by
    intro y
    obtain ⟨n, hn⟩ := hsurjΨ y
    obtain ⟨s, z, hz⟩ := Concrete.isColimit_exists_rep _ hcolim n
    refine ⟨s, z, ?_⟩
    have hz' : ((moduleStalkRing B X Λ t).map
        (Sigma.desc fun a : {a // a ∈ s} => Sigma.ι G a.1.as)) z = n := hz
    have hcomp : ((moduleStalkRing B X Λ t).map
        ((Sigma.desc fun a : {a // a ∈ s} => Sigma.ι G a.1.as) ≫ Ψ)) z = y := by
      rw [Functor.map_comp, ConcreteCategory.comp_apply, hz', hn]
    exact hcomp
  refine ⟨T.sup fun y => (hmem y).choose, ?_⟩
  rw [ModuleCat.epi_iff_range_eq_top]
  refine eq_top_iff.2 (le_trans (le_of_eq hT.symm) (Submodule.span_le.2 ?_))
  intro y hy
  exact range_moduleStalkRing_map_sigma_desc_le B X Λ G Ψ t
    (Finset.le_sup (Finset.mem_coe.1 hy)) (hmem y).choose_spec

variable [CompactSpace X.1] [QuasiSeparatedSpace X.1]

private abbrev constructibleModuleSheavesMaxRing (B : BigEtaleSite.{u}) (X : B.Scheme)
    (Λ : Type r) [Ring Λ] :
    ObjectProperty (Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{max (u + 1) r} Λ)) :=
  fun F => IsConstructibleModuleSheaf B X Λ F

private instance isWeakSerreClass_constructibleModuleSheavesMaxRing :
    (constructibleModuleSheavesMaxRing B X Λ).IsWeakSerreClass :=
  SmallEtale.isWeakSerreClass_isConstructibleModuleSheaf.{u, r, r} B X Λ

private instance isClosedUnderFiniteCoproducts_constructibleModuleSheavesMaxRing :
    (constructibleModuleSheavesMaxRing B X Λ).IsClosedUnderFiniteCoproducts := by
  have : (constructibleModuleSheavesMaxRing B X Λ).IsClosedUnderBinaryCoproducts :=
    ObjectProperty.IsClosedUnderColimitsOfShape.mk' (fun _ ⟨H, hH⟩ =>
      (constructibleModuleSheavesMaxRing B X Λ).prop_of_iso
        ((biprod.isoCoprod _ _).trans (HasColimit.isoOfNatIso (diagramIsoPair H)).symm)
        ((constructibleModuleSheavesMaxRing B X Λ).prop_biprod (hH ⟨.left⟩) (hH ⟨.right⟩)))
  exact ObjectProperty.IsClosedUnderFiniteCoproducts.mk'

private theorem isConstructible_setOf_not_isZero_etaleStalk_cokernel_ring (B : BigEtaleSite.{u})
    (X : B.Scheme) (Λ : Type r) [Ring Λ] [IsNoetherianRing Λ] [CompactSpace X.1]
    [QuasiSeparatedSpace X.1]
    {F F' : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{max (u + 1) r} Λ)}
    (f : F' ⟶ F)
    (hF' : IsConstructibleModuleSheaf B X Λ F') (hF : IsConstructibleModuleSheaf B X Λ F) :
    Topology.IsConstructible {x : X.1 | ∃ t : GeometricPoint X.1, t.LiesOver x ∧
      ¬ IsZero (etaleStalk B X.1 X.property t (cokernel f).obj)} := by
  have := preservesFilteredColimits_forget_moduleCatMax_of_ring.{u, r} Λ
  exact isConstructible_support_moduleSheaf_of_ring.{u, r, max (u + 1) r} B X Λ _
    ((constructibleModuleSheavesMaxRing B X Λ).prop_cokernel f hF' hF)

/-- **The finite generation step of the proof of Stacks 095N, abstracted.** Let `X` be
quasi-compact and quasi-separated, `Λ` an arbitrary ring, `Ψ` an epimorphism of sheaves of
`Λ`-modules onto `F` from a direct sum indexed by an arbitrary set. Suppose that the stalks of `F`
are finitely generated and that, for every finite subsum, the set of points over which the
cokernel of the restricted map has a nonzero geometric stalk is constructible. Then the
restriction of `Ψ` to some finite subsum is already an epimorphism. -/
theorem exists_finset_epi_sigma_desc_of_isFG_of_isConstructible
    (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type r) [Ring Λ]
    [CompactSpace X.1] [QuasiSeparatedSpace X.1]
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{max (u + 1) r} Λ))
    {A : Type max (u + 1) r}
    (M : A → Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{max (u + 1) r} Λ))
    (Ψ : (∐ M) ⟶ F) [Epi Ψ]
    (hfg : ∀ t : GeometricPoint X.1, ModuleCat.isFG Λ
      (((geometricPointSitePoint B X.1 X.property t).sheafFiber
        (A := ModuleCat.{max (u + 1) r} Λ)).obj F))
    (hcons : ∀ s : Finset (Discrete A), Topology.IsConstructible
      {x : X.1 | ∃ t : GeometricPoint X.1, t.LiesOver x ∧
        ¬ IsZero (etaleStalk B X.1 X.property t
          (cokernel ((Sigma.desc fun a : {a // a ∈ s} => Sigma.ι M a.1.as) ≫ Ψ)).obj)}) :
    ∃ s : Finset (Discrete A),
      Epi ((Sigma.desc fun a : {a // a ∈ s} => Sigma.ι M a.1.as) ≫ Ψ) := by
  classical
  let T : Finset (Discrete A) → Set X.1 := fun s =>
    {x : X.1 | ∃ t : GeometricPoint X.1, t.LiesOver x ∧
      ¬ IsZero (etaleStalk B X.1 X.property t
        (cokernel ((Sigma.desc fun a : {a // a ∈ s} => Sigma.ι M a.1.as) ≫ Ψ)).obj)}
  have hTiff : ∀ (s : Finset (Discrete A)) (x : X.1), x ∈ T s ↔ ∃ t : GeometricPoint X.1,
      t.LiesOver x ∧ ¬ Epi ((moduleStalkRing B X Λ t).map
        ((Sigma.desc fun a : {a // a ∈ s} => Sigma.ι M a.1.as) ≫ Ψ)) := fun s x =>
    exists_congr fun t => and_congr_right fun _ =>
      not_congr (isZero_etaleStalk_cokernel_iff_ring B X Λ _ t)
  have hanti : ∀ {s s' : Finset (Discrete A)}, s ≤ s' → T s' ⊆ T s := by
    intro s s' hss x hx
    obtain ⟨t, ht, hne⟩ := (hTiff s' x).1 hx
    refine (hTiff s x).2 ⟨t, ht, fun hepi => hne ?_⟩
    have hr := range_moduleStalkRing_map_sigma_desc_le B X Λ M Ψ t hss
    rw [ModuleCat.epi_iff_range_eq_top] at hepi ⊢
    exact eq_top_iff.2 (le_trans (le_of_eq hepi.symm) hr)
  have hempty : (⋂ s, T s) = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.2 fun x hx => ?_
    obtain ⟨s, hs⟩ := exists_finset_epi_moduleStalkRing_map_sigma
      B X Λ F M Ψ (GeometricPoint.ofPoint X.1 x) (hfg _)
    obtain ⟨t, ht, hne⟩ := (hTiff s x).1 (Set.mem_iInter.1 hx s)
    refine hne ((ModuleCat.epi_iff_surjective _).2 ?_)
    exact surjective_map_of_natIsoOfCoefficients (ModuleCat.{max (u + 1) r} Λ)
      (etaleStalkPresheafFunctorIsoOfEqBase B X.1 X.property
        (ht.trans (GeometricPoint.ofPoint_liesOver X.1 x).symm) (ModuleCat.{max (u + 1) r} Λ))
      ((Sigma.desc fun a : {a // a ∈ s} => Sigma.ι M a.1.as) ≫ Ψ).hom
      ((ModuleCat.epi_iff_surjective _).1 hs)
  obtain ⟨s, hs⟩ : ∃ s : Finset (Discrete A), T s = ∅ := by
    by_contra hcon
    have hne : ∀ s : Finset (Discrete A),
        (WithConstructibleTopology.ofConstructible ⁻¹' T s).Nonempty := by
      intro s
      obtain ⟨y, hy⟩ := Set.nonempty_iff_ne_empty.2 fun h => hcon ⟨s, h⟩
      exact ⟨WithConstructibleTopology.toConstructible y, by simpa using hy⟩
    have hcl : ∀ s : Finset (Discrete A),
        IsClosed (WithConstructibleTopology.ofConstructible ⁻¹' T s) := fun s => by
      rw [← isOpen_compl_iff, ← Set.preimage_compl,
        WithConstructibleTopology.isOpen_preimage_ofConstructible,
        constructibleTopology_eq_generateFrom_isConstructible ↥X.1]
      exact TopologicalSpace.isOpen_generateFrom_of_mem (hcons s).compl
    obtain ⟨y, hy⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      (fun s : Finset (Discrete A) => WithConstructibleTopology.ofConstructible ⁻¹' T s)
      (fun s s' => ⟨s ∪ s', Set.preimage_mono (hanti le_sup_left),
        Set.preimage_mono (hanti le_sup_right)⟩) hne (fun s => (hcl s).isCompact) hcl
    have hmem : WithConstructibleTopology.ofConstructible y ∈ ⋂ s, T s :=
      Set.mem_iInter.2 fun s => Set.mem_iInter.1 hy s
    rwa [hempty] at hmem
  refine ⟨s, ?_⟩
  have hstalk : ∀ t : GeometricPoint X.1, Function.Surjective
      ((etaleStalkPresheafFunctor B X.1 X.property t (ModuleCat.{max (u + 1) r} Λ)).map
        ((Sigma.desc fun a : {a // a ∈ s} => Sigma.ι M a.1.as) ≫ Ψ).hom) := by
    intro t
    by_contra hcon
    have hx : t.hom default ∈ T s :=
      (hTiff s _).2 ⟨t, rfl, fun hepi => hcon ((ModuleCat.epi_iff_surjective _).1 hepi)⟩
    rwa [hs] at hx
  have := preservesFilteredColimitsOfSize_forget_moduleCatMax_of_ring.{u, r} Λ
  have := isLocallySurjective_of_surjective_etaleStalkMapOfCoefficients B X.1 X.property
    (ModuleCat.{max (u + 1) r} Λ) _ hstalk
  exact inferInstance


/-- **The finite generation step of the proof of Stacks 095N, over an arbitrary Noetherian
ring.** Let `X` be quasi-compact and quasi-separated, `F` a constructible sheaf of `Λ`-modules and
`Ψ` an epimorphism onto `F` from a direct sum of constructible sheaves indexed by an arbitrary set.
Then the restriction of `Ψ` to some finite subsum is already an epimorphism. The proof is that of
`AlgebraicGeometry.exists_finset_epi_sigma_desc_of_isConstructibleModuleSheaf`, which uses no
commutativity. -/
theorem exists_finset_epi_sigma_desc_of_isConstructibleModuleSheaf_of_ring
    (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type r) [Ring Λ] [IsNoetherianRing Λ]
    [CompactSpace X.1] [QuasiSeparatedSpace X.1]
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{max (u + 1) r} Λ))
    {A : Type max (u + 1) r}
    (M : A → Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{max (u + 1) r} Λ))
    (Ψ : (∐ M) ⟶ F) [Epi Ψ] (hM : ∀ a, IsConstructibleModuleSheaf B X Λ (M a))
    (hF : IsConstructibleModuleSheaf B X Λ F) :
    ∃ s : Finset (Discrete A),
      Epi ((Sigma.desc fun a : {a // a ∈ s} => Sigma.ι M a.1.as) ≫ Ψ) :=
  exists_finset_epi_sigma_desc_of_isFG_of_isConstructible B X Λ F M Ψ
    (fun t => isFG_moduleStalkRing_of_isConstructibleModuleSheaf B X Λ F hF t)
    (fun _s => isConstructible_setOf_not_isZero_etaleStalk_cokernel_ring B X Λ _
      ((constructibleModuleSheavesMaxRing B X Λ).prop_coproduct fun a => hM a.1.as) hF)

omit [IsNoetherianRing Λ] in
/-- The generator `j_{U!}\underline{\Lambda}_U` at a quasi-compact quasi-separated étale object of
a quasi-compact quasi-separated scheme is flat constructible, for an arbitrary ring. -/
private theorem isConstructibleFlatModuleSheaf_moduleShriekConstant_of_isQCQSEtaleObject
    (U : SmallEtale B X.1 X.property) (hU : IsQCQSEtaleObject B X U) :
    IsConstructibleFlatModuleSheaf B X Λ (moduleShriekConstant.{u, r, r} B X Λ U) := by
  have hc : CompactSpace U.obj.left.obj := hU.1
  have hq : QuasiSeparatedSpace U.obj.left.obj := hU.2
  exact isConstructibleFlatModuleSheaf_moduleShriekConstant_of_ring B X Λ U

/-- **Finite sums of generators refine epimorphisms onto constructible sheaves, over an arbitrary
Noetherian ring.** Let `X` be a quasi-compact quasi-separated scheme of a big étale site, `Λ` a
Noetherian ring, not necessarily commutative, and `p : Z ⟶ H` an epimorphism of sheaves of
`Λ`-modules on `X_étale` with `H` constructible. Then there are finitely many quasi-compact
quasi-separated étale objects `V_i` and a map `f : ⊕ j_{V_i!}\underline{\Lambda}_{V_i} ⟶ Z` with
`f ≫ p` an epimorphism. This is Tag 093B part (2) followed by the finite generation step of
Tag 095P, as in the proof of Tag 095N. -/
theorem exists_finite_epi_comp_sigma_moduleShriekConstant_qcqs_of_ring (B : BigEtaleSite.{u})
    (X : B.Scheme) (Λ : Type r) [Ring Λ] [IsNoetherianRing Λ]
    [CompactSpace X.1] [QuasiSeparatedSpace X.1]
    {H Z : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{max (u + 1) r} Λ)}
    (p : Z ⟶ H) [Epi p] (hH : IsConstructibleModuleSheaf B X Λ H) :
    ∃ (n : ℕ) (V : Fin n → SmallEtale B X.1 X.property),
      (∀ i, IsQCQSEtaleObject B X (V i)) ∧
        ∃ f : (∐ fun i : Fin n => moduleShriekConstant.{u, r, r} B X Λ (V i)) ⟶ Z,
          Epi (f ≫ p) := by
  classical
  obtain ⟨A, U, hU, q, hq⟩ := exists_epi_sigma_moduleShriekConstant_qcqs_of_ring B X Λ Z
  have hΨ : Epi (q ≫ p) := epi_comp _ _
  obtain ⟨s, hs⟩ := exists_finset_epi_sigma_desc_of_isConstructibleModuleSheaf_of_ring B X Λ H
    (fun a => moduleShriekConstant.{u, r, r} B X Λ (U a)) (q ≫ p)
    (fun a => isConstructibleModuleSheaf_of_isConstructibleFlatModuleSheaf B X Λ
      (isConstructibleFlatModuleSheaf_moduleShriekConstant_of_isQCQSEtaleObject B X Λ _ (hU a)))
    hH
  refine ⟨s.card, fun i => U (s.equivFin.symm i).1.as, fun i => hU _,
    (Sigma.reindex s.equivFin.symm
        (fun a : {a // a ∈ s} =>
          moduleShriekConstant.{u, r, r} B X Λ (U a.1.as))).hom ≫
      (Sigma.desc fun a : {a // a ∈ s} =>
        Sigma.ι (fun a => moduleShriekConstant.{u, r, r} B X Λ (U a)) a.1.as) ≫ q, ?_⟩
  rw [Category.assoc, Category.assoc]
  infer_instance

/-- **Constructible flat sheaves cover epimorphisms onto constructible sheaves**, over an arbitrary
Noetherian ring and on a quasi-compact quasi-separated scheme: the covering hypothesis of the
bounded above resolution engine
`Stacks.Homology.BoundedAboveResolution.exists_quasiIso_isStrictlyLE_of_coversEpis`, with the
class of constructible sheaves as ambient weak Serre class and the class of constructible flat
sheaves as the class of terms. The covering objects are finite direct sums of generators
`j_{V!}\underline{\Lambda}_V` at quasi-compact quasi-separated étale objects. -/
@[sga "4½ Rapport 4.8" "more general"]
theorem coversEpis_isConstructibleFlatModuleSheaf (B : BigEtaleSite.{u}) (X : B.Scheme)
    (Λ : Type r) [Ring Λ] [IsNoetherianRing Λ] [CompactSpace X.1] [QuasiSeparatedSpace X.1] :
    Stacks.Homology.BoundedAboveResolution.CoversEpis
      (isConstructibleModuleSheafProperty.{u, max (u + 1) r, r} B X Λ)
      (IsConstructibleFlatModuleSheaf B X Λ) := by
  intro V W f hf hW
  obtain ⟨n, U, hU, g, hg⟩ :=
    exists_finite_epi_comp_sigma_moduleShriekConstant_qcqs_of_ring B X Λ f hW
  have hflat : IsConstructibleFlatModuleSheaf B X Λ
      (∐ fun i : Fin n => moduleShriekConstant.{u, r, r} B X Λ (U i)) :=
    isConstructibleFlatModuleSheaf_sigma B X Λ _ fun i =>
      isConstructibleFlatModuleSheaf_moduleShriekConstant_of_isQCQSEtaleObject B X Λ _ (hU i)
  exact ⟨_, g, hflat, isConstructibleModuleSheaf_of_isConstructibleFlatModuleSheaf B X Λ hflat,
    hg⟩

end FiniteGeneration

section Biproducts

attribute [local instance] smallEtaleHasSheafifyModuleMax_of_ring
  smallEtaleHasColimitsOfSizeModuleMax_of_ring
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring
  SmallEtale.hasWeakSheafify_over_moduleCat_ring

/-- A binary biproduct of constructible flat sheaves of `Λ`-modules is constructible flat. -/
theorem isConstructibleFlatModuleSheaf_biprod (B : BigEtaleSite.{u}) (X : B.Scheme)
    (Λ : Type r) [Ring Λ]
    {C E : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) r} Λ)}
    (hC : IsConstructibleFlatModuleSheaf B X Λ C) (hE : IsConstructibleFlatModuleSheaf B X Λ E) :
    IsConstructibleFlatModuleSheaf B X Λ (C ⊞ E) := by
  have : ∀ T : B.Scheme,
      HasSheafify (SmallEtale.topology B T.obj T.property) (ModuleCat.{max (u + 1) r} Λ) :=
    fun T ↦ SmallEtale.hasSheafify_moduleCat.{u, r, r} B T Λ
  have : HasFiniteBiproducts (Sheaf (SmallEtale.topology B X.obj X.property)
    (ModuleCat.{max (u + 1) r} Λ)) := Abelian.hasFiniteBiproducts
  let e2 : Fin 2 ≃ WalkingPair :=
    { toFun := fun i => if i = 0 then WalkingPair.left else WalkingPair.right
      invFun := fun j => match j with
        | WalkingPair.left => 0
        | WalkingPair.right => 1
      left_inv := fun i => by fin_cases i <;> rfl
      right_inv := fun j => by cases j <;> rfl }
  let F : Fin 2 → Sheaf (SmallEtale.topology B X.obj X.property)
      (ModuleCat.{max (u + 1) r} Λ) := fun i => pairFunction C E (e2 i)
  have hF : IsConstructibleFlatModuleSheaf B X Λ (∐ F) :=
    isConstructibleFlatModuleSheaf_sigma B X Λ F fun i => by fin_cases i <;> assumption
  let b := biproduct.bicone (pairFunction C E)
  have hb : b.toBinaryBicone.IsBilimit :=
    (Bicone.toBinaryBiconeIsBilimit b).symm (biproduct.isBilimit (pairFunction C E))
  let ebiprod : C ⊞ E ≅ ∐ (pairFunction C E) :=
    (biprod.uniqueUpToIso C E hb).symm.trans (biproduct.isoCoproduct (pairFunction C E))
  let ereindex : ∐ F ≅ ∐ (pairFunction C E) :=
    Sigma.whiskerEquiv (f := F) (g := pairFunction C E) e2 (fun _ => Iso.refl _)
  exact isConstructibleFlatModuleSheaf_congr B X Λ (ereindex ≪≫ ebiprod.symm) hF

end Biproducts

end AlgebraicGeometry

end
