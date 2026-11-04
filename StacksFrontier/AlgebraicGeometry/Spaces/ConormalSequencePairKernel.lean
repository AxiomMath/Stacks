module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleFirstOrderIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSequenceDefiningIdealFibreSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealSheafMapSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleChartCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackId
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ThickeningSharpLiftChartKernel
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftDifferenceSection
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftDifferenceRingSurjectivity

/-!
# Kernel scratch
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)


section Injective

variable {C : Type*} [Category C] {J : GrothendieckTopology C}

private theorem app_apply_app_apply_of_comp_eq_id {R R' : Sheaf J RingCat.{u}} (a : R ⟶ R')
    (r : R' ⟶ R) (h : a ≫ r = 𝟙 R) (U : Cᵒᵖ) (z : R.obj.obj U) :
    (r.hom.app U).hom ((a.hom.app U).hom z) = z :=
  ConcreteCategory.congr_hom (congrArg (fun m : R ⟶ R => m.hom.app U) h) z

/-- A morphism of sheaves of rings with a retraction is injective on sections. -/
theorem injective_app_of_comp_eq_id {R R' : Sheaf J RingCat.{u}} (a : R ⟶ R') (r : R' ⟶ R)
    (h : a ≫ r = 𝟙 R) (U : Cᵒᵖ) : Function.Injective (a.hom.app U).hom := by
  intro x y hxy
  rw [← app_apply_app_apply_of_comp_eq_id a r h U x, ← app_apply_app_apply_of_comp_eq_id a r h U y,
    hxy]

end Injective

section Sharp

private theorem comp_comp_comp_inv_eq_id {C : Type*} [Category C] {P Q R T : C}
    (a : P ⟶ Q) (b : Q ⟶ R) (c : R ⟶ T) (d : P ⟶ T) (hd : IsIso d) (h : a ≫ b ≫ c = d) :
    a ≫ b ≫ c ≫ @inv _ _ _ _ d hd = 𝟙 P := by
  subst h
  calc a ≫ b ≫ c ≫ inv (a ≫ b ≫ c) = (a ≫ b ≫ c) ≫ inv (a ≫ b ≫ c) := by
        simp only [Category.assoc]
    _ = 𝟙 P := IsIso.hom_inv_id _

variable {X Y : AlgebraicSpaces B S hS}

/-- The structure map `f^♯ : 𝒪_Y ⟶ f_*𝒪_X` of an isomorphism `f` of algebraic spaces is a split
monomorphism of sheaves of rings. -/
theorem exists_structureSharp_comp_eq_id (f : X ⟶ Y) [IsIso f] :
    ∃ r, structureSharp B S hS f ≫ r = 𝟙 _ := by
  have key : ∀ k : Y ⟶ Y, k = 𝟙 Y → IsIso (structureSharp B S hS k) := by
    rintro _ rfl
    infer_instance
  have hk := key (inv f ≫ f) (IsIso.inv_hom_id f)
  refine ⟨(Stacks.Sheaves.ToposPushforward.pushforwardRingFunctor
      (smallToposMorphismTypeU B S hS f)).map (structureSharp B S hS (inv f)) ≫
    pushforwardRingSheafCompHom B S hS (inv f) f (structureRingSheaf B S hS Y) ≫
    @inv _ _ _ _ (structureSharp B S hS (inv f ≫ f)) hk, ?_⟩
  exact comp_comp_comp_inv_eq_id _ _ _ _ hk
    (structureSharp_comp_pushforwardRingSheafCompHom B S hS (inv f) f)

end Sharp

section Pushforward

variable {X X' : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)

/-- **The direct image along `g` is fully faithful** when `Z ⊆ X` is a thickening and `i ≫ g` is a
closed immersion: `i_*` is an equivalence of small étale topoi, `(i ≫ g)_*` is fully faithful
by Stacks 04E5, part (1), and `(i ≫ g)_* ≅ i_* ⋙ g_*`. -/
noncomputable def fullyFaithfulSmallEtalePushforwardOfThickening
    (hZ : IsThickening B S hS X Z.1) (g : X ⟶ X')
    (hg : IsClosedImmersion B S hS (subspaceInclusion B S hS X Z ≫ g).hom) :
    (smallToposMorphismTypeU B S hS g).pushforward.FullyFaithful := by
  have hA := fullyFaithfulSmallEtalePushforwardOfIsClosedImmersion B S hS
    (subspaceInclusion B S hS X Z) Z.2.2
  haveI := hA.full
  haveI := hA.faithful
  haveI := essSurj_smallEtalePushforward_of_isThickening B S hS Z hZ
  haveI : (smallToposMorphismTypeU B S hS
      (subspaceInclusion B S hS X Z)).pushforward.IsEquivalence :=
    { }
  have hJ := (fullyFaithfulSmallEtalePushforwardOfIsClosedImmersion B S hS _ hg).ofIso
    (smallToposMorphismTypeU_comp B S hS (subspaceInclusion B S hS X Z) g).symm
  exact ((smallToposMorphismTypeU B S hS
      (subspaceInclusion B S hS X Z)).pushforward.asEquivalence.fullyFaithfulInverse.comp hJ).ofIso
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (smallToposMorphismTypeU B S hS
        (subspaceInclusion B S hS X Z)).pushforward.asEquivalence.counitIso _ ≪≫
      Functor.leftUnitor _)

end Pushforward

section Counit

variable {X X' : AlgebraicSpaces B S hS}

/-- When the direct image of sheaves of sets is fully faithful, the counit of the ring-level
adjunction `g^{-1} ⊣ g_*` is injective on sections. -/
theorem injective_app_ringCounit_of_fullyFaithful (g : X ⟶ X')
    (hg : (smallToposMorphismTypeU B S hS g).pushforward.FullyFaithful)
    (T : Sheaf (SmallEtale.topology B S hS X.1) RingCat.{u}) (U : (SmallEtale B S hS X.1)ᵒᵖ) :
    Function.Injective
      ((Stacks.Sheaves.ToposPushforward.ringCounit (smallToposMorphismTypeU B S hS g) T).hom.app
        U) :=
  have := hg.full
  have := hg.faithful
  fun _ _ h ↦ Stacks.Sheaves.ToposPullback.injective_sections_of_iso
    ((asIso (smallToposMorphismTypeU B S hS g).adj.counit).app
      (Sheaf.ringSheaf.{u, u, u + 1} T)) U h

end Counit

section Pair

variable {X X' : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)
  (W : ClosedSubspaces B S hS X'.1) (g : X ⟶ X')
  (f : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
    (⟨W.1.toFunctor, W.2.1⟩ : AlgebraicSpaces B S hS))

/-- The structure map of `g` followed by the direct image along `g` of the structure map of the
inclusion of `Z`: the morphism `𝒪_{X'} ⟶ g_*i_*𝒪_Z` of sheaves of rings. -/
noncomputable abbrev structureSharpThroughSubspace :=
  structureSharp B S hS g ≫
    (Stacks.Sheaves.ToposPushforward.pushforwardRingFunctor
      (smallToposMorphismTypeU B S hS g)).map
      (structureSharp B S hS (subspaceInclusion B S hS X Z))

/-- `AlgebraicGeometry.Space.structureSharpThroughSubspace`, followed by the comparison of iterated
direct images, is the structure map of `i ≫ g` (Stacks 03G8). -/
theorem structureSharpThroughSubspace_comp_pushforwardRingSheafCompHom :
    structureSharpThroughSubspace B S hS Z g ≫
        pushforwardRingSheafCompHom B S hS (subspaceInclusion B S hS X Z) g _ =
      structureSharp B S hS (subspaceInclusion B S hS X Z ≫ g) :=
  (Category.assoc _ _ _).trans (structureSharp_comp_pushforwardRingSheafCompHom B S hS _ g)

private theorem app_comp_eq_zero_iff {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R R' R'' : Sheaf J RingCat.{u}} (a : R ⟶ R') (b : R' ⟶ R'') (r : R'' ⟶ R')
    (hb : b ≫ r = 𝟙 R') (U : Cᵒᵖ) (x : R.obj.obj U) :
    ((a ≫ b).hom.app U).hom x = 0 ↔ (a.hom.app U).hom x = 0 := by
  show (b.hom.app U).hom ((a.hom.app U).hom x) = 0 ↔ _
  constructor
  · intro h
    exact injective_app_of_comp_eq_id b r hb U (h.trans (map_zero _).symm)
  · intro h
    rw [h, map_zero]

private theorem map_comp_comp_inv_comp_map_eq_id {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {x y : C} {p : D} (s : x ⟶ y) (r : y ⟶ x) (hom : F.obj y ⟶ p)
    (inv : p ⟶ F.obj y) (h1 : hom ≫ inv = 𝟙 _) (h2 : s ≫ r = 𝟙 x) :
    (F.map s ≫ hom) ≫ inv ≫ F.map r = 𝟙 _ := by
  rw [Category.assoc, ← Category.assoc hom, h1, Category.id_comp, ← F.map_comp, h2, F.map_id]

/-- **The kernel of `𝒪_{X'} ⟶ g_*i_*𝒪_Z` is the defining ideal of `W`**, when `g` restricts to an
isomorphism of `Z` onto `W`. -/
theorem structureSharpThroughSubspace_app_eq_zero_iff [IsIso f]
    (hsq : subspaceInclusion B S hS X Z ≫ g = f ≫ subspaceInclusion B S hS X' W)
    (V : (SmallEtale B S hS X'.1)ᵒᵖ) (c : ToType ((structureRingSheaf B S hS X').obj.obj V)) :
    ((structureSharpThroughSubspace B S hS Z g).hom.app V).hom c = 0 ↔
        c ∈ definingIdealAt B S hS X' W V := by
  have h1 := app_comp_eq_zero_iff (structureSharpThroughSubspace B S hS Z g)
    (pushforwardRingSheafCompHom B S hS (subspaceInclusion B S hS X Z) g _)
    (pushforwardRingSheafCompInv B S hS (subspaceInclusion B S hS X Z) g _)
    (pushforwardRingSheafCompHom_comp_inv B S hS _ g _) V c
  rw [structureSharpThroughSubspace_comp_pushforwardRingSheafCompHom] at h1
  obtain ⟨r, hr⟩ := exists_structureSharp_comp_eq_id B S hS
    (X := ⟨Z.1.toFunctor, Z.2.1⟩) (Y := ⟨W.1.toFunctor, W.2.1⟩) f
  have key : ∀ k : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ X',
      k = f ≫ subspaceInclusion B S hS X' W →
      (((structureSharp B S hS k).hom.app V).hom c = 0 ↔
        ((structureSharp B S hS (subspaceInclusion B S hS X' W)).hom.app V).hom c = 0) := by
    rintro _ rfl
    rw [← structureSharp_comp_pushforwardRingSheafCompHom B S hS f
      (subspaceInclusion B S hS X' W)]
    refine app_comp_eq_zero_iff _ _ (pushforwardRingSheafCompInv B S hS f _ _ ≫
        (Stacks.Sheaves.ToposPushforward.pushforwardRingFunctor
          (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X' W))).map r) ?_ V c
    exact map_comp_comp_inv_comp_map_eq_id _ _ _ _ _
      (pushforwardRingSheafCompHom_comp_inv B S hS f _ _) hr
  exact h1.symm.trans ((key _ hsq).trans (mem_definingIdealAt_iff B S hS X' W V c).symm)

/-- If `g` restricts to an isomorphism of `Z` onto a closed subspace of `X'`, then `i ≫ g` is a
closed immersion. -/
theorem isClosedImmersion_subspaceInclusion_comp [IsIso f]
    (hsq : subspaceInclusion B S hS X Z ≫ g = f ≫ subspaceInclusion B S hS X' W) :
    IsClosedImmersion B S hS (subspaceInclusion B S hS X Z ≫ g).hom := by
  rw [hsq]
  exact isClosedImmersion_comp B S hS f.hom W.1.ι (isClosedImmersion_of_isIso B S hS f.hom) W.2.2

/-- The inverse-image form of `g^♯` followed by `i^♯ : 𝒪_X ⟶ i_*𝒪_Z` is the inverse image of
`AlgebraicGeometry.Space.structureSharpThroughSubspace` followed by the counit of
`g^{-1} ⊣ g_*`. -/
theorem structureSharpRingInverseImage_comp_structureSharp :
    structureSharpRingInverseImage B S hS g ≫
        structureSharp B S hS (subspaceInclusion B S hS X Z) =
      (Stacks.Sheaves.ToposPushforward.inverseImageRingFunctor
          (smallToposMorphismTypeU B S hS g)).map (structureSharpThroughSubspace B S hS Z g) ≫
        (Stacks.Sheaves.ToposPushforward.ringImageAdjunction
          (smallToposMorphismTypeU B S hS g)).counit.app _ :=
  ((Stacks.Sheaves.ToposPushforward.ringImageAdjunction
      (smallToposMorphismTypeU B S hS g)).homEquiv_naturality_right_symm _ _).symm.trans
    ((Stacks.Sheaves.ToposPushforward.ringImageAdjunction
      (smallToposMorphismTypeU B S hS g)).homEquiv_counit _ _ _)

/-- **A section of `g^{-1}𝒪_{X'}` whose image under `g^♯` lies in the defining ideal of `Z` comes
from a section of `g^{-1}𝓙`**, with `𝓙` the defining ideal of `W`. -/
theorem exists_inverseImage_definingIdealSheaf_eq_of_mem (hZ : IsThickening B S hS X Z.1)
    [IsIso f] (hsq : subspaceInclusion B S hS X Z ≫ g = f ≫ subspaceInclusion B S hS X' W)
    (U : (SmallEtale B S hS X.1)ᵒᵖ) (c : (structureRingSheafInverseImage B S hS g).obj.obj U)
    (hc : ((structureSharpRingInverseImage B S hS g).hom.app U).hom c ∈
      definingIdealAt B S hS X Z U) :
    ∃ m : (Sheaf.sectionsFunctor (SmallEtale.topology B S hS X.1) U).obj
        ((smallToposMorphismTypeU B S hS g).inverseImage.obj
          (Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS X')
            (definingIdealSheaf B S hS X' W).toSheafOfModules)),
      (Sheaf.sectionsFunctor (SmallEtale.topology B S hS X.1) U).map
        ((smallToposMorphismTypeU B S hS g).inverseImage.map
          (Stacks.Sheaves.ToposPullback.submoduleInclSheafSets
            (definingIdealSheaf B S hS X' W))) m = c := by
  have hff := fullyFaithfulSmallEtalePushforwardOfThickening B S hS Z hZ g
    (isClosedImmersion_subspaceInclusion_comp B S hS Z W g f hsq)
  refine (Stacks.Sheaves.ToposPullback.existsUnique_sections_of_isPullback
    (J := SmallEtale.topology B S hS X.1) (smallToposMorphismTypeU B S hS g).inverseImage
    (structureSharpThroughSubspace B S hS Z g)
    (Stacks.Sheaves.ToposPullback.submoduleInclSheafSets (definingIdealSheaf B S hS X' W))
    (Stacks.Sheaves.ToposPullback.isPullback_submoduleInclSheafSets
        (structureSharpThroughSubspace B S hS Z g)
      (definingIdealSheaf B S hS X' W)
      (fun V a ↦
          (structureSharpThroughSubspace_app_eq_zero_iff B S hS Z W g f hsq V a).symm)) U c
          ?_).exists
  refine injective_app_ringCounit_of_fullyFaithful B S hS g hff _ U ?_
  refine Eq.trans ?_ (map_zero _).symm
  have hc' := (mem_definingIdealAt_iff B S hS X Z U _).1 hc
  have key := ConcreteCategory.congr_hom (congrArg (fun m ↦ m.hom.app U)
    (structureSharpRingInverseImage_comp_structureSharp B S hS Z g)) c
  exact key.symm.trans hc'


private theorem eq_comp_of_comp_eq {C : Type*} [Category C] {P Q R : C} (a : P ⟶ Q)
    (b : Q ⟶ R) (b' : R ⟶ Q) (c : P ⟶ R) (h : a ≫ b = c) (hb : b ≫ b' = 𝟙 Q) :
    a = c ≫ b' := by
  rw [← h, Category.assoc, hb, Category.comp_id]

private theorem isLocallySurjective_of_surjective {C : Type*} [Category C]
    {J : GrothendieckTopology C} {R R' : Sheaf J RingCat.{u}} (φ : R ⟶ R')
    (h : ∀ U, Function.Surjective (φ.hom.app U)) : Sheaf.IsLocallySurjective φ where
  imageSieve_mem {U} y := by
    have : Presheaf.imageSieve φ.hom y = ⊤ := by
      ext V g
      simp only [Sieve.top_apply, iff_true]
      exact h _ _
    rw [this]
    exact J.top_mem _

private theorem isLocallySurjective_of_comp_eq_id {C : Type*} [Category C]
    {J : GrothendieckTopology C} {R R' : Sheaf J RingCat.{u}} (φ : R ⟶ R') (ψ : R' ⟶ R)
    (h : ψ ≫ φ = 𝟙 R') : Sheaf.IsLocallySurjective φ :=
  isLocallySurjective_of_surjective φ fun U y ↦
    ⟨(ψ.hom.app U).hom y, app_apply_app_apply_of_comp_eq_id ψ φ h U y⟩

private theorem isLocallySurjective_comp_of_comp_eq_id {C : Type*} [Category C]
    {J : GrothendieckTopology C} {R R' R'' : Sheaf J RingCat.{u}} (a : R ⟶ R') (b : R' ⟶ R'')
    (b' : R'' ⟶ R') (ha : Sheaf.IsLocallySurjective a) (hb : b' ≫ b = 𝟙 R'') :
    Sheaf.IsLocallySurjective (a ≫ b) :=
  have := isLocallySurjective_of_comp_eq_id b b' hb
  Sheaf.isLocallySurjective_comp a b

/-- `AlgebraicGeometry.Space.structureSharpThroughSubspace` is the structure map of `i ≫ g`
followed by the comparison of iterated direct images. -/
theorem structureSharpThroughSubspace_eq_structureSharp_comp :
    structureSharpThroughSubspace B S hS Z g = structureSharp B S hS
        (subspaceInclusion B S hS X Z ≫ g) ≫
      pushforwardRingSheafCompInv B S hS (subspaceInclusion B S hS X Z) g _ :=
  eq_comp_of_comp_eq _ _ _ _
      (structureSharpThroughSubspace_comp_pushforwardRingSheafCompHom B S hS Z g)
    (pushforwardRingSheafCompHom_comp_inv B S hS _ g _)

/-- `𝒪_{X'} ⟶ g_*i_*𝒪_Z` is locally surjective, `i ≫ g` being a closed immersion. -/
theorem isLocallySurjective_structureSharpThroughSubspace [IsIso f]
    (hsq : subspaceInclusion B S hS X Z ≫ g = f ≫ subspaceInclusion B S hS X' W) :
    Sheaf.IsLocallySurjective (structureSharpThroughSubspace B S hS Z g) := by
  rw [structureSharpThroughSubspace_eq_structureSharp_comp]
  exact isLocallySurjective_comp_of_comp_eq_id _ _ _
    (isLocallySurjective_structureSharp B S hS _
      (isClosedImmersion_subspaceInclusion_comp B S hS Z W g f hsq))
    (pushforwardRingSheafCompHom_comp_inv B S hS (subspaceInclusion B S hS X Z) g _)

/-- `g^{-1}𝒪_{X'} ⟶ 𝒪_X ⟶ i_*𝒪_Z` is locally surjective. -/
theorem isLocallySurjective_structureSharpRingInverseImage_comp (hZ : IsThickening B S hS X Z.1)
    [IsIso f] (hsq : subspaceInclusion B S hS X Z ≫ g = f ≫ subspaceInclusion B S hS X' W) :
    Sheaf.IsLocallySurjective (structureSharpRingInverseImage B S hS g ≫
      structureSharp B S hS (subspaceInclusion B S hS X Z)) := by
  have hff := fullyFaithfulSmallEtalePushforwardOfThickening B S hS Z hZ g
    (isClosedImmersion_subspaceInclusion_comp B S hS Z W g f hsq)
  have := hff.full
  have := hff.faithful
  have hP := isLocallySurjective_structureSharpThroughSubspace B S hS Z W g f hsq
  have hL : Sheaf.IsLocallySurjective ((Stacks.Sheaves.ToposPushforward.inverseImageRingFunctor
      (smallToposMorphismTypeU B S hS g)).map (structureSharpThroughSubspace B S hS Z g)) := by
    have := Stacks.Sheaves.ToposPullback.isLocallySurjective_inverseImage_map
      (smallToposMorphismTypeU B S hS g)
      ((sheafCompose (SmallEtale.topology B S hS X'.1) (forget RingCat.{u})).map
        (structureSharpThroughSubspace B S hS Z g))
    exact ⟨fun {_} y ↦ Presheaf.imageSieve_mem (SmallEtale.topology B S hS X.1)
      ((smallToposMorphismTypeU B S hS g).inverseImage.map
        ((sheafCompose (SmallEtale.topology B S hS X'.1) (forget RingCat.{u})).map
          (structureSharpThroughSubspace B S hS Z g))).hom y⟩
  have hC : Sheaf.IsLocallySurjective ((Stacks.Sheaves.ToposPushforward.ringImageAdjunction
      (smallToposMorphismTypeU B S hS g)).counit.app
        ((Stacks.Sheaves.ToposPushforward.pushforwardRingFunctor (smallToposMorphismTypeU B S hS
          (subspaceInclusion B S hS X Z))).obj
              (structureRingSheaf B S hS ⟨Z.1.toFunctor, Z.2.1⟩))) :=
    isLocallySurjective_of_surjective _ fun U ↦
      ((Sheaf.sectionsFunctor (SmallEtale.topology B S hS X.1) U).mapIso
        ((asIso (smallToposMorphismTypeU B S hS g).adj.counit).app
          (Sheaf.ringSheaf.{u, u, u + 1} ((Stacks.Sheaves.ToposPushforward.pushforwardRingFunctor
            (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z))).obj
              (structureRingSheaf B S hS ⟨Z.1.toFunctor, Z.2.1⟩))))).toEquiv.surjective
  rw [structureSharpRingInverseImage_comp_structureSharp]
  exact @Sheaf.isLocallySurjective_comp _ _ _ _ _ _ _ _ _ _ _ _ _ _ hL hC

/-- **Every section of `𝒪_X` is locally `g^♯(c)` plus a section of the defining ideal of
`Z`.** -/
theorem exists_sub_mem_definingIdealAt (hZ : IsThickening B S hS X Z.1)
    [IsIso f] (hsq : subspaceInclusion B S hS X Z ≫ g = f ≫ subspaceInclusion B S hS X' W)
    (U : (SmallEtale B S hS X.1)ᵒᵖ) (x : ToType ((structureRingSheaf B S hS X).obj.obj U)) :
    ∃ T ∈ SmallEtale.topology B S hS X.1 U.unop, ∀ (V : SmallEtale B S hS X.1)
      (h : V ⟶ U.unop), T h → ∃ c : (structureRingSheafInverseImage B S hS g).obj.obj (op V),
        ((structureRingSheaf B S hS X).obj.map h.op).hom x -
          ((structureSharpRingInverseImage B S hS g).hom.app (op V)).hom c ∈
            definingIdealAt B S hS X Z (op V) := by
  have := isLocallySurjective_structureSharpRingInverseImage_comp B S hS Z W g f hZ hsq
  refine ⟨Presheaf.imageSieve (structureSharpRingInverseImage B S hS g ≫
      structureSharp B S hS (subspaceInclusion B S hS X Z)).hom
      (((structureSharp B S hS (subspaceInclusion B S hS X Z)).hom.app U).hom x),
    Presheaf.imageSieve_mem _ _ _, fun V h hh ↦ ?_⟩
  obtain ⟨c, hc⟩ := hh
  refine ⟨c, (mem_definingIdealAt_iff B S hS X Z (op V) _).2 ?_⟩
  rw [map_sub, structureSharp_app_apply_map]
  exact sub_eq_zero.2 hc.symm


end Pair


section IdealMap

variable {X X' : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)
  (W : ClosedSubspaces B S hS X'.1) (g : X ⟶ X')
  (f : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
    (⟨W.1.toFunctor, W.2.1⟩ : AlgebraicSpaces B S hS))
  (hsq : subspaceInclusion B S hS X Z ≫ g = f ≫ subspaceInclusion B S hS X' W)

/-- The section of `g_*𝓘` attached to a section `s` of `𝓙` by the chartwise map of defining ideal
sheaves, read in `g_*𝒪_X`, is `g^♯(s)`. -/
theorem map_submoduleInclSheafSets_moduleFMapSection_idealSheafFMap
    (V : SmallEtale B S hS X'.1)
    (s : (definingIdealSheaf B S hS X' W).toSheafOfModules.val.obj (op V)) :
    ((smallEtaleDirectImage B S hS g).map
        (Stacks.Sheaves.ToposPullback.submoduleInclSheafSets
          (definingIdealSheaf B S hS X Z))).hom.app (op V)
        (moduleFMapSection B S hS g (definingIdealSheaf B S hS X Z).toSheafOfModules
          (definingIdealSheaf B S hS X' W).toSheafOfModules
              (idealSheafFMap B S hS Z W g f hsq) V s) =
      ((structureSharp B S hS g).hom.app (op V)).hom s.1 := by
  refine moduleChartProjection_ext B S hS g V (structureSetSheaf B S hS X) (fun j ↦ ?_)
  refine Eq.trans (NatTrans.naturality_apply (moduleChartProjection B S hS g V j)
    (Stacks.Sheaves.ToposPullback.submoduleInclSheafSets (definingIdealSheaf B S hS X Z)) _) ?_
  refine Eq.trans (congrArg (fun x ↦ ((Sheaf.sectionsFunctor _ j.right).map
    (Stacks.Sheaves.ToposPullback.submoduleInclSheafSets (definingIdealSheaf B S hS X Z))) x)
    (moduleChartProjection_app_moduleFMapSection B S hS g _ _ _ V j s)) ?_
  exact (moduleChartProjection_app_structureSharp B S hS g V j s.1).symm

/-- The transpose of `AlgebraicGeometry.Space.idealSheafMap` along `g^* ⊣ g_*` is the morphism
built from the chartwise map `AlgebraicGeometry.Space.idealSheafFMap`. -/
theorem homEquiv_idealSheafMap :
    (modulePullbackAdjunction B S hS g).homEquiv _ _ (idealSheafMap B S hS Z W g f hsq) =
      moduleFMapHom B S hS g (definingIdealSheaf B S hS X Z).toSheafOfModules
        (definingIdealSheaf B S hS X' W).toSheafOfModules (idealSheafFMap B S hS Z W g f hsq) :=
  Equiv.apply_symm_apply _ _

/-- On underlying sheaves of sets, the transpose of `AlgebraicGeometry.Space.idealSheafMap`
followed by the direct image of the inclusion of the defining ideal sheaf of `Z` is the
inclusion of the defining ideal sheaf of `W` followed by the structure map of `g`. -/
theorem moduleSheafFunctor_map_homEquiv_idealSheafMap_comp :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X')).map
        ((modulePullbackAdjunction B S hS g).homEquiv _ _ (idealSheafMap B S hS Z W g f hsq)) ≫
      (smallToposMorphismTypeU B S hS g).pushforward.map
        (Stacks.Sheaves.ToposPullback.submoduleInclSheafSets (definingIdealSheaf B S hS X Z)) =
    Stacks.Sheaves.ToposPullback.submoduleInclSheafSets (definingIdealSheaf B S hS X' W) ≫
      structureSharpSet B S hS g := by
  rw [homEquiv_idealSheafMap]
  refine Sheaf.hom_ext_sections fun V s ↦ ?_
  exact map_submoduleInclSheafSets_moduleFMapSection_idealSheafFMap B S hS Z W g f hsq V.unop s

/-- The inverse-image form of the structure map, as a morphism of sheaves of sets, is the
transpose of the direct-image form. -/
theorem homEquiv_structureSharpRingInverseImage_set :
    (smallToposMorphismTypeU B S hS g).adj.homEquiv _ _
        ((sheafCompose (SmallEtale.topology B S hS X.1) (forget RingCat.{u})).map
          (structureSharpRingInverseImage B S hS g)) =
      structureSharpSet B S hS g := by
  have h : (sheafCompose (SmallEtale.topology B S hS X.1) (forget RingCat.{u})).map
      (structureSharpRingInverseImage B S hS g) = structureSharpInverseImageSet B S hS g :=
    Sheaf.hom_ext_sections fun V x ↦ structureSharpRingInverseImage_app B S hS g V x
  rw [h]
  exact homEquiv_structureSharpInverseImageSet B S hS g

/-- The comparison of the inverse image of sheaves of sets of the defining ideal sheaf of `W`
with the inverse image of modules: the transpose along `g^{-1} ⊣ g_*` of the unit of
`g^* ⊣ g_*`, read on underlying sheaves of sets. -/
noncomputable def inverseImageDefiningIdealToPullback :
    (smallToposMorphismTypeU B S hS g).inverseImage.obj
        (Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS X')
          (definingIdealSheaf B S hS X' W).toSheafOfModules) ⟶
      Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS X)
        ((modulePullback B S hS g).obj (definingIdealSheaf B S hS X' W).toSheafOfModules) :=
  ((smallToposMorphismTypeU B S hS g).adj.homEquiv _ _).symm
    ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X')).map
      ((modulePullbackAdjunction B S hS g).unit.app _))

/-- **The inverse image of the inclusion of the defining ideal of `W`, followed by `g^♯`,
factors through `AlgebraicGeometry.Space.idealSheafMap`.**  On underlying sheaves of sets on
the site of `X`. -/
theorem inverseImage_map_submoduleInclSheafSets_comp_structureSharpRingInverseImage :
    (smallToposMorphismTypeU B S hS g).inverseImage.map
        (Stacks.Sheaves.ToposPullback.submoduleInclSheafSets (definingIdealSheaf B S hS X' W)) ≫
      (sheafCompose (SmallEtale.topology B S hS X.1) (forget RingCat.{u})).map
        (structureSharpRingInverseImage B S hS g) =
    inverseImageDefiningIdealToPullback B S hS W g ≫
      (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map
        (idealSheafMap B S hS Z W g f hsq) ≫
      Stacks.Sheaves.ToposPullback.submoduleInclSheafSets (definingIdealSheaf B S hS X Z) := by
  have e : (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X')).map
        ((modulePullbackAdjunction B S hS g).homEquiv _ _ (idealSheafMap B S hS Z W g f hsq)) =
      (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X')).map
          ((modulePullbackAdjunction B S hS g).unit.app _) ≫
        (smallToposMorphismTypeU B S hS g).pushforward.map
          ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map
            (idealSheafMap B S hS Z W g f hsq)) :=
    (congrArg (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X')).map
      (Adjunction.homEquiv_unit _ _ _ _)).trans (Functor.map_comp _ _ _)
  refine ((smallToposMorphismTypeU B S hS g).adj.homEquiv _ _).injective ?_
  refine ((Adjunction.homEquiv_naturality_left _ _ _).trans ?_).trans
    (Adjunction.homEquiv_naturality_right _ _ _).symm
  refine (congrArg (fun φ ↦ Stacks.Sheaves.ToposPullback.submoduleInclSheafSets
    (definingIdealSheaf B S hS X' W) ≫ φ)
        (homEquiv_structureSharpRingInverseImage_set B S hS g)).trans ?_
  refine (moduleSheafFunctor_map_homEquiv_idealSheafMap_comp B S hS Z W g f hsq).symm.trans ?_
  refine Eq.trans ?_ (congrArg (fun φ ↦ φ ≫ (smallToposMorphismTypeU B S hS g).pushforward.map
    ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map
      (idealSheafMap B S hS Z W g f hsq) ≫
      Stacks.Sheaves.ToposPullback.submoduleInclSheafSets (definingIdealSheaf B S hS X Z)))
    (Equiv.apply_symm_apply _ _).symm)
  refine (congrArg (fun φ ↦ φ ≫ (smallToposMorphismTypeU B S hS g).pushforward.map
    (Stacks.Sheaves.ToposPullback.submoduleInclSheafSets
        (definingIdealSheaf B S hS X Z))) e).trans ?_
  exact (Category.assoc _ _ _).trans (congrArg (fun φ ↦ _ ≫ φ) (Functor.map_comp _ _ _).symm)

end IdealMap

section Vanishing

variable {X X' : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)
  (W : ClosedSubspaces B S hS X'.1) (g : X ⟶ X')
  (f : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
    (⟨W.1.toFunctor, W.2.1⟩ : AlgebraicSpaces B S hS))

/-- **A morphism out of the defining ideal of `Z` killed by the image of `g^*𝓘_W` kills every
section `g^♯(c)` lying in the defining ideal of `Z`.**  Here `Z ⊆ X` is a thickening, `g`
restricts to an isomorphism `f` of `Z` onto the closed subspace `W` of `X'`, and `c` is a
section of `g^{-1}𝒪_{X'}`.  This is the sheaf form of the ring-level statement that for
`A → B` with `A/J ≅ B/I`, an element of `A` whose image lies in `I` lies in `J`. -/
theorem app_structureSharpRingInverseImage_eq_zero_of_idealSheafMap_comp_eq_zero
    (hZ : IsThickening B S hS X Z.1) [IsIso f]
    (hsq : subspaceInclusion B S hS X Z ≫ g = f ≫ subspaceInclusion B S hS X' W)
    {N : Modules.{u, u} B S hS X.1 X.2} (κ : (definingIdealSheaf B S hS X Z).toSheafOfModules ⟶ N)
    (hκ : idealSheafMap B S hS Z W g f hsq ≫ κ = 0)
    (U : (SmallEtale B S hS X.1)ᵒᵖ) (c : (structureRingSheafInverseImage B S hS g).obj.obj U)
    (hc : ((structureSharpRingInverseImage B S hS g).hom.app U).hom c ∈
      definingIdealAt B S hS X Z U) :
    (κ.val.app U).hom ⟨_, hc⟩ = 0 := by
  obtain ⟨m, hm⟩ := exists_inverseImage_definingIdealSheaf_eq_of_mem B S hS Z W g f hZ hsq U c hc
  have key : ((structureSharpRingInverseImage B S hS g).hom.app U).hom
        (((smallToposMorphismTypeU B S hS g).inverseImage.map
          (Stacks.Sheaves.ToposPullback.submoduleInclSheafSets
            (definingIdealSheaf B S hS X' W))).hom.app U m) =
      ((Stacks.Sheaves.ToposPullback.submoduleInclSheafSets
          (definingIdealSheaf B S hS X Z)).hom.app U
        (((idealSheafMap B S hS Z W g f hsq).val.app U).hom
          ((inverseImageDefiningIdealToPullback B S hS W g).hom.app U m))) :=
    congrArg (fun φ ↦ φ.hom.app U m)
      (inverseImage_map_submoduleInclSheafSets_comp_structureSharpRingInverseImage B S hS Z W g f
        hsq)
  have hm' : ((smallToposMorphismTypeU B S hS g).inverseImage.map
      (Stacks.Sheaves.ToposPullback.submoduleInclSheafSets
        (definingIdealSheaf B S hS X' W))).hom.app U m = c := hm
  rw [hm'] at key
  have he : (⟨_, hc⟩ : (definingIdealSheaf B S hS X Z).toSheafOfModules.val.obj U) =
      ((idealSheafMap B S hS Z W g f hsq).val.app U).hom
        ((inverseImageDefiningIdealToPullback B S hS W g).hom.app U m) :=
    Subtype.ext key
  rw [he]
  exact congrArg (fun φ : (modulePullback B S hS g).obj
      (definingIdealSheaf B S hS X' W).toSheafOfModules ⟶ N ↦
    (φ.val.app U).hom ((inverseImageDefiningIdealToPullback B S hS W g).hom.app U m)) hκ

end Vanishing



end AlgebraicGeometry.Space

end
