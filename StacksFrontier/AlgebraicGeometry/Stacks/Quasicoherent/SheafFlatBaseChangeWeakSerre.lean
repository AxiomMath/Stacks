module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.SheafificationAdjunctIso
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FppfSheafFromSheafFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleExactAssociatedModule
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleLocalBijectivity
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedPullback09US
public import StacksFrontier.AlgebraicGeometry.QcohLimits.ClosedUnderKernels
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentAssociatedModule
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentClosure

/-!
# The flat base change property on étale sheaves, through the comparison of sheaves

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids and `φ : z ⟶ x` an arrow of `𝒳`
over a morphism of schemes `a : W ⟶ U`. For an étale sheaf of `𝒪_𝒳`-modules `F`, the comparison
map of sheaves `c^♯_φ : a_{small}^*(F|_{U_ét}) ⟶ F|_{W_ét}` of **Stacks 06WC** is natural in `F`:
it is a natural transformation `sheafRestrictComparison` from the restriction to `U_ét` followed
by the inverse image of sheaves of modules to the restriction to `W_ét`. The flat base change
property of **Stacks 0762** says it is an isomorphism at `F` whenever `a` is flat
(`AlgebraicGeometry.Stack.hasSheafFlatBaseChangeProperty_iff_isIso_sheafRestrictComparison`).

Both functors are right exact — restriction is exact and the inverse image is a left adjoint —
and the restriction to `W_ét` is exact, which is what the closure properties of the flat base
change property under cokernels, extensions and colimits come from (**Stacks 0764** parts (2)
and (4)).

## Main definitions

* `AlgebraicGeometry.Stack.sheafRestrictComparison`: the comparison map of sheaves, as a natural
  transformation of functors on `Mod(𝒳_ét, 𝒪_𝒳)`.

## Main results

* `AlgebraicGeometry.Stack.hasSheafFlatBaseChangeProperty_iff_isIso_sheafRestrictComparison`.
* `AlgebraicGeometry.Stack.mono_map_sheafifiedPullbackComparison_restrict`: along a flat
  morphism, the inverse image keeps monomorphisms between locally quasi-coherent modules.
* `AlgebraicGeometry.Stack.isWeakSerreClass_isLocallyQuasicoherentWithSheafFlatBaseChange` and
  `AlgebraicGeometry.Stack.isWeakSerreClass_lqcohSheafFbcEtaleModules`: **Stacks 0771 part (2),
  the étale half.**

## References

* [Stacks Project, Tag 06WC](https://stacks.math.columbia.edu/tag/06WC)
* [Stacks Project, Tag 0762](https://stacks.math.columbia.edu/tag/0762)
* [Stacks Project, Tag 0764](https://stacks.math.columbia.edu/tag/0764)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u v w j jv

namespace CategoryTheory.NatTrans

/-- A natural transformation between functors which preserve the colimit of `K` is an isomorphism
at the point of a colimit cocone of `K` as soon as it is one at every object of the diagram. -/
theorem isIso_app_of_isColimit {C : Type*} [Category C] {D : Type*} [Category D]
    {J : Type*} [Category J] {Φ Ψ : C ⥤ D} (η : Φ ⟶ Ψ) {K : J ⥤ C} {c : Cocone K}
    (hc : IsColimit c) [PreservesColimit K Φ] [PreservesColimit K Ψ]
    (hη : ∀ i, IsIso (η.app (K.obj i))) :
    IsIso (η.app c.pt) := by
  have hΦ : IsColimit (Φ.mapCocone c) := isColimitOfPreserves Φ hc
  have hwi : ∀ i : J, IsIso ((Functor.whiskerLeft K η).app i) := hη
  have hw : IsIso (Functor.whiskerLeft K η) := NatIso.isIso_of_isIso_app _
  let α : K ⋙ Φ ≅ K ⋙ Ψ := asIso (Functor.whiskerLeft K η)
  have hΦ' : IsColimit ((Cocone.precompose α.hom).obj (Ψ.mapCocone c)) :=
    (IsColimit.precomposeHomEquiv α _).symm (isColimitOfPreserves Ψ hc)
  have heq : η.app c.pt = (IsColimit.coconePointUniqueUpToIso hΦ hΦ').hom := by
    refine hΦ.hom_ext fun i => ?_
    rw [IsColimit.comp_coconePointUniqueUpToIso_hom]
    exact η.naturality (c.ι.app i)
  rw [heq]
  infer_instance

/-- A natural transformation between functors which preserve the limit of `K` is an isomorphism
at the point of a limit cone of `K` as soon as it is one at every object of the diagram. -/
theorem isIso_app_of_isLimit {C : Type*} [Category C] {D : Type*} [Category D]
    {J : Type*} [Category J] {Φ Ψ : C ⥤ D} (η : Φ ⟶ Ψ) {K : J ⥤ C} {c : Cone K}
    (hc : IsLimit c) [PreservesLimit K Φ] [PreservesLimit K Ψ]
    (hη : ∀ i, IsIso (η.app (K.obj i))) :
    IsIso (η.app c.pt) := by
  have hΨ : IsLimit (Ψ.mapCone c) := isLimitOfPreserves Ψ hc
  have hwi : ∀ i : J, IsIso ((Functor.whiskerLeft K η).app i) := hη
  have hw : IsIso (Functor.whiskerLeft K η) := NatIso.isIso_of_isIso_app _
  let α : K ⋙ Φ ≅ K ⋙ Ψ := asIso (Functor.whiskerLeft K η)
  have hΨ' : IsLimit ((Cone.postcompose α.hom).obj (Φ.mapCone c)) :=
    (IsLimit.postcomposeHomEquiv α _).symm (isLimitOfPreserves Φ hc)
  have heq : η.app c.pt = (IsLimit.conePointUniqueUpToIso hΨ' hΨ).hom := by
    refine hΨ.hom_ext fun i => ?_
    rw [IsLimit.conePointUniqueUpToIso_hom_comp]
    exact (η.naturality (c.π.app i)).symm
  rw [heq]
  infer_instance

end CategoryTheory.NatTrans

namespace CategoryTheory.ShortComplex

/-- In a morphism of short exact sequences of an abelian category whose second and third
components are isomorphisms, the first component is an isomorphism: it is a monomorphism, and the
lift of `S₂.f ≫ φ.τ₂⁻¹` through the kernel `S₁.f` of `S₁.g` is a right inverse. -/
theorem isIso₁_of_shortExact_of_isIso₂₃ {C : Type*} [Category C] [Abelian C]
    {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂) (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact)
    [IsIso φ.τ₂] [IsIso φ.τ₃] : IsIso φ.τ₁ := by
  have := h₁.mono_f
  have := h₂.mono_f
  have : Mono φ.τ₁ := mono_of_mono_fac φ.comm₁₂
  have hg : inv φ.τ₂ ≫ S₁.g = S₂.g ≫ inv φ.τ₃ := by
    rw [IsIso.eq_comp_inv, Category.assoc, ← φ.comm₂₃, IsIso.inv_hom_id_assoc]
  let l : S₂.X₁ ⟶ S₁.X₁ := h₁.exact.lift (S₂.f ≫ inv φ.τ₂) (by
    rw [Category.assoc, hg, ← Category.assoc, S₂.zero, zero_comp])
  have hl : l ≫ S₁.f = S₂.f ≫ inv φ.τ₂ := h₁.exact.lift_f _ _
  have hr : l ≫ φ.τ₁ = 𝟙 _ := by
    rw [← cancel_mono S₂.f, Category.assoc, φ.comm₁₂, ← Category.assoc, hl, Category.assoc,
      IsIso.inv_hom_id, Category.comp_id, Category.id_comp]
  have : IsSplitEpi φ.τ₁ := ⟨⟨l, hr⟩⟩
  exact isIso_of_mono_of_isSplitEpi _

end CategoryTheory.ShortComplex

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-- **The comparison map of sheaves of Stacks 06WC, as a natural transformation.** For an arrow
`φ : z ⟶ x` of `𝒳` over `a : W ⟶ U`, the map `a_{small}^*(F|_{U_ét}) ⟶ F|_{W_ét}` of étale sheaves
of modules, natural in the étale sheaf of `𝒪_𝒳`-modules `F`: at `F` it is the adjunct
`AlgebraicGeometry.Stack.sheafifiedRestrictComparison` of the comparison map of presheaves. -/
noncomputable def sheafRestrictComparison {x z : 𝒳} (φ : z ⟶ x) :
    restrictSheafToSmallEtale.{u, v, w, u} B E h S hS p hp x ⋙
        sheafifiedPullbackComparison B E h S hS p hp (etaleTopology B)
          (etaleTopology_le_topology B) φ ⟶
      restrictSheafToSmallEtale.{u, v, w, u} B E h S hS p hp z where
  app F := sheafifiedRestrictComparison B E h S hS p hp F.val φ
    ((restrictSheafToSmallEtale.{u, v, w, u} B E h S hS p hp z).obj F).isSheaf
  naturality F G α := by
    have hnat := restrictModulePullbackComparison_naturality B E h S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B) φ α.val
    have hl := (PresheafOfModules.sheafificationAdjunction
        (𝟙 (SmallEtale.structureSheaf E (p.obj z).left.1
          (contains_base B E h S hS p z)).obj)).homEquiv_naturality_left_symm
      (Y := (restrictSheafToSmallEtale.{u, v, w, u} B E h S hS p hp z).obj G)
      ((PresheafOfModules.pullback.{u}
          (smallEtaleStructureComparison B E h S hS p hp φ (etaleTopology B)
            (etaleTopology_le_topology B))).map
        ((restrictModuleToSmallEtaleFunctor.{u, v, w, u} B E h S hS p hp (etaleTopology B)
          (etaleTopology_le_topology B) x).map α.val))
      (restrictModulePullbackComparison B E h S hS p hp φ (etaleTopology B)
        (etaleTopology_le_topology B) G.val)
    have hr := (PresheafOfModules.sheafificationAdjunction
        (𝟙 (SmallEtale.structureSheaf E (p.obj z).left.1
          (contains_base B E h S hS p z)).obj)).homEquiv_naturality_right_symm
      (restrictModulePullbackComparison B E h S hS p hp φ (etaleTopology B)
        (etaleTopology_le_topology B) F.val)
      ((restrictSheafToSmallEtale.{u, v, w, u} B E h S hS p hp z).map α)
    exact hl.symm.trans ((congrArg (((PresheafOfModules.sheafificationAdjunction
        (𝟙 (SmallEtale.structureSheaf E (p.obj z).left.1
          (contains_base B E h S hS p z)).obj)).homEquiv _
      ((restrictSheafToSmallEtale.{u, v, w, u} B E h S hS p hp z).obj G)).symm) hnat).trans hr)

/-- The comparison map of sheaves at `F` is the adjunct of the comparison map of presheaves. -/
theorem sheafRestrictComparison_app {x z : 𝒳} (φ : z ⟶ x)
    (F : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B))) :
    (sheafRestrictComparison B E h S hS p hp φ).app F =
      ((PresheafOfModules.sheafificationAdjunction
        (𝟙 (SmallEtale.structureSheaf E (p.obj z).left.1
          (contains_base B E h S hS p z)).obj)).homEquiv _
        ((restrictSheafToSmallEtale.{u, v, w, u} B E h S hS p hp z).obj F)).symm
        (restrictModulePullbackComparison B E h S hS p hp φ (etaleTopology B)
          (etaleTopology_le_topology B) F.val) :=
  rfl

/-- At module universe `u`, the comparison map formed at a free module universe is the comparison
map of **Stacks 06WC**. -/
theorem restrictModulePullbackComparisonUnivLE_eq {x z : 𝒳} (φ : z ⟶ x)
    (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology)
    (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp τ hτ).obj) :
    restrictModulePullbackComparisonUnivLE B E h S hS p hp φ τ hτ F =
      restrictModulePullbackComparison B E h S hS p hp φ τ hτ F :=
  rfl

/-- **The flat base change property of Stacks 0762, for an étale sheaf, is invertibility of the
comparison map of sheaves along every arrow over a flat morphism.** -/
theorem hasSheafFlatBaseChangeProperty_iff_isIso_sheafRestrictComparison
    (F : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B))) :
    HasSheafFlatBaseChangeProperty B E h S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B) F.val ↔
      ∀ {z x : 𝒳} (φ : z ⟶ x), Flat (B.inclusion.map (p.map φ).left) →
        IsIso ((sheafRestrictComparison B E h S hS p hp φ).app F) := by
  refine forall_congr' fun z => forall_congr' fun x => forall_congr' fun φ =>
    imp_congr_right fun _ => ?_
  have : (SmallEtale.topology E (p.obj z).left.1
      (contains_base B E h S hS p z)).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _
  rw [restrictModulePullbackComparisonUnivLE_eq]
  exact (PresheafOfModules.isIso_sheafificationAdjunction_homEquiv_symm_iff
    (𝟙 (SmallEtale.structureSheaf E (p.obj z).left.1 (contains_base B E h S hS p z)).obj)
    (G := (restrictSheafToSmallEtale.{u, v, w, u} B E h S hS p hp z).obj F)
    (restrictModulePullbackComparison B E h S hS p hp φ (etaleTopology B)
      (etaleTopology_le_topology B) F.val)).symm

section Closure

variable [HasWeakSheafify (associatedTopology B S hS p (etaleTopology B)) AddCommGrpCat.{u}]
  [(associatedTopology B S hS p (etaleTopology B)).WEqualsLocallyBijective AddCommGrpCat.{u}]
  {x z : 𝒳} (φ : z ⟶ x)

/-- The inverse image of sheaves of modules along `φ` is a left adjoint. -/
instance isLeftAdjoint_sheafifiedPullbackComparison :
    (sheafifiedPullbackComparison B E h S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B) φ).IsLeftAdjoint :=
  (sheafifiedPullbackComparisonAdjunction B E h S hS p hp (etaleTopology B)
    (etaleTopology_le_topology B) φ).isLeftAdjoint

/-- The inverse image of sheaves of modules along `φ` preserves colimits, being a left
adjoint. -/
instance preservesColimits_sheafifiedPullbackComparison :
    PreservesColimitsOfSize.{j, jv} (sheafifiedPullbackComparison B E h S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B) φ) :=
  (sheafifiedPullbackComparisonAdjunction B E h S hS p hp (etaleTopology B)
    (etaleTopology_le_topology B) φ).leftAdjoint_preservesColimits

/-- The comparison map of sheaves is an isomorphism at a zero object. -/
theorem isIso_sheafRestrictComparison_app_of_isZero
    {F : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B))} (hF : IsZero F) :
    IsIso ((sheafRestrictComparison B E h S hS p hp φ).app F) := by
  have h₁ := Functor.map_isZero (restrictSheafToSmallEtale.{u, v, w, u} B E h S hS p hp x ⋙
    sheafifiedPullbackComparison B E h S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B) φ) hF
  have h₂ := Functor.map_isZero (restrictSheafToSmallEtale.{u, v, w, u} B E h S hS p hp z) hF
  exact ⟨0, h₁.eq_of_src _ _, h₂.eq_of_src _ _⟩

omit [HasWeakSheafify (associatedTopology B S hS p (etaleTopology B)) AddCommGrpCat.{u}]
  [(associatedTopology B S hS p (etaleTopology B)).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **The comparison map of sheaves is an isomorphism at a cokernel** of a map between modules at
which it is an isomorphism: both functors it compares are right exact. -/
theorem isIso_sheafRestrictComparison_app_of_isColimit
    {F₁ F₂ : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B))} {f : F₁ ⟶ F₂} {k : CokernelCofork f} (hk : IsColimit k)
    (h₁ : IsIso ((sheafRestrictComparison B E h S hS p hp φ).app F₁))
    (h₂ : IsIso ((sheafRestrictComparison B E h S hS p hp φ).app F₂)) :
    IsIso ((sheafRestrictComparison B E h S hS p hp φ).app k.pt) :=
  NatTrans.isIso_app_of_isColimit (sheafRestrictComparison B E h S hS p hp φ) hk
    (by rintro (_ | _) <;> assumption)

omit [HasWeakSheafify (associatedTopology B S hS p (etaleTopology B)) AddCommGrpCat.{u}]
  [(associatedTopology B S hS p (etaleTopology B)).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **The comparison map of sheaves is an isomorphism at a kernel**, provided the source functor
preserves that kernel; the target functor, restriction to the small étale site, is exact. -/
theorem isIso_sheafRestrictComparison_app_of_isLimit
    {F₁ F₂ : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B))} {f : F₁ ⟶ F₂} {k : KernelFork f} (hk : IsLimit k)
    [PreservesLimit (parallelPair f 0)
      (restrictSheafToSmallEtale.{u, v, w, u} B E h S hS p hp x ⋙
        sheafifiedPullbackComparison B E h S hS p hp (etaleTopology B)
          (etaleTopology_le_topology B) φ)]
    (h₁ : IsIso ((sheafRestrictComparison B E h S hS p hp φ).app F₁))
    (h₂ : IsIso ((sheafRestrictComparison B E h S hS p hp φ).app F₂)) :
    IsIso ((sheafRestrictComparison B E h S hS p hp φ).app k.pt) :=
  NatTrans.isIso_app_of_isLimit (sheafRestrictComparison B E h S hS p hp φ) hk
    (by rintro (_ | _) <;> assumption)

/-- For a short exact sequence `T`, the source functor of the comparison map of sheaves sends it to
a right exact sequence, and the target functor sends it to a short exact one. -/
private theorem exact_epi_shortExact_map_sheafRestrictComparison
    {T : ShortComplex (SheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)))} (hT : T.ShortExact) :
    (T.map (restrictSheafToSmallEtale.{u, v, w, u} B E h S hS p hp x ⋙
      sheafifiedPullbackComparison B E h S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B) φ)).Exact ∧
    Epi (T.map (restrictSheafToSmallEtale.{u, v, w, u} B E h S hS p hp x ⋙
      sheafifiedPullbackComparison B E h S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B) φ)).g ∧
    (T.map (restrictSheafToSmallEtale.{u, v, w, u} B E h S hS p hp z)).ShortExact := by
  let P := restrictSheafToSmallEtale.{u, v, w, u} B E h S hS p hp x ⋙
    sheafifiedPullbackComparison B E h S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B) φ
  have := hT.epi_g
  exact ⟨hT.exact.map_of_epi_of_preservesCokernel P inferInstance inferInstance,
    (inferInstance : Epi (P.map T.g)), hT.map_of_exact _⟩

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for `IsIso` and `Mono` on maps of short complexes of sheaves of modules
/-- **The comparison map of sheaves is an isomorphism at an extension** of two modules at which
it is an isomorphism. The source functor is right exact and the target functor exact, so the
comparison is a map from a right exact sequence to a short exact one, isomorphic at the ends; the
first map of the source sequence is then a monomorphism, and the five lemma applies. -/
theorem isIso_sheafRestrictComparison_app_of_shortExact
    {T : ShortComplex (SheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)))} (hT : T.ShortExact)
    (h₁ : IsIso ((sheafRestrictComparison B E h S hS p hp φ).app T.X₁))
    (h₃ : IsIso ((sheafRestrictComparison B E h S hS p hp φ).app T.X₃)) :
    IsIso ((sheafRestrictComparison B E h S hS p hp φ).app T.X₂) := by
  obtain ⟨hPe, _, hR⟩ := exact_epi_shortExact_map_sheafRestrictComparison B E h S hS p hp φ hT
  let ψ := ShortComplex.mapNatTrans T (sheafRestrictComparison B E h S hS p hp φ)
  have : IsIso ψ.τ₁ := h₁
  have : IsIso ψ.τ₃ := h₃
  have : Mono (T.map _).f := hR.mono_f
  have : Mono (T.map _).f := mono_of_mono_fac ψ.comm₁₂.symm
  exact ShortComplex.isIso₂_of_shortExact_of_isIso₁₃ ψ ⟨hPe⟩ hR

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for `Mono` through the associated-module and pullback functors
omit [HasWeakSheafify (associatedTopology B S hS p (etaleTopology B)) AddCommGrpCat.{u}]
  [(associatedTopology B S hS p (etaleTopology B)).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Along a flat morphism, the inverse image of sheaves of modules keeps the image `f^a` of a
monomorphism `f` of modules on the scheme a monomorphism: it is `(a^*f)^a`, and `a^*` is exact for
`a` flat (**Stacks 02N4**). -/
private theorem mono_map_sheafifiedPullbackComparison_associatedModule
    (hflat : Flat (B.inclusion.map (p.map φ).left))
    {M₁ M₂ : (p.obj x).left.1.Modules} (f : M₁ ⟶ M₂) [Mono f] :
    Mono ((SmallEtale.associatedModule E (p.obj x).left.1
      (contains_base B E h S hS p x) ⋙ sheafifiedPullbackComparison B E h S hS p hp
        (etaleTopology B) (etaleTopology_le_topology B) φ).map f) := by
  have := preservesFiniteLimits_pullback_of_flat (B.inclusion.map (p.map φ).left)
  have := SmallEtale.preservesFiniteLimits_associatedModule E (p.obj z).left.1
    (contains_base B E h S hS p z)
  let N := associatedModuleSmallEtaleBaseChangeIso B E h S hS p hp (etaleTopology B)
    (etaleTopology_le_topology B) φ
  have : Mono (N.hom.app _ ≫ (Scheme.Modules.pullback (B.inclusion.map (p.map φ).left) ⋙
      SmallEtale.associatedModule E (p.obj z).left.1 (contains_base B E h S hS p z)).map f) :=
    mono_comp' (@IsIso.mono_of_iso _ _ _ _ (N.hom.app _) (Iso.isIso_hom (N.app _)))
      (Functor.map_mono _ _)
  rw [← N.hom.naturality f] at this
  exact @mono_of_mono _ _ _ _ _ _ (N.hom.app _) this

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for `Mono` through the restriction functors is expensive
set_option maxHeartbeats 800000 in
-- instance search for `Mono` and finite-limit preservation through the restriction functors
/-- **The inverse image of sheaves of modules along a flat morphism is injective on
monomorphisms between quasi-coherent modules.** For `φ : z ⟶ x` over a flat morphism `a` and a
monomorphism `ι : F₁ ⟶ F₂` of locally quasi-coherent étale sheaves of `𝒪_𝒳`-modules, the
inverse image along `a_{small}` of the restriction of `ι` to the small étale site of the scheme
below `x` is a monomorphism.

Both restrictions are `𝓕^a` for quasi-coherent modules `𝓕` on the scheme, by **Stacks 03DX**, and
the restriction of `ι` is `ι₀^a` for a map `ι₀` of quasi-coherent modules, `𝓕 ↦ 𝓕^a` being fully
faithful on them; `ι₀` is a monomorphism since its kernel is quasi-coherent and `𝓕 ↦ 𝓕^a` is
exact and faithful there. The inverse image of `ι₀^a` is `(a^*ι₀)^a`, and `a^*` is exact for `a`
flat (**Stacks 02N4**). -/
theorem mono_map_sheafifiedPullbackComparison_restrict
    (hflat : Flat (B.inclusion.map (p.map φ).left))
    {F₁ F₂ : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B))} (ι : F₁ ⟶ F₂) [Mono ι]
    (h₁ : IsLocallyQuasicoherent B E h S hS p hp F₁.val)
    (h₂ : IsLocallyQuasicoherent B E h S hS p hp F₂.val) :
    Mono ((restrictSheafToSmallEtale.{u, v, w, u} B E h S hS p hp x ⋙
      sheafifiedPullbackComparison B E h S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B) φ).map ι) := by
  obtain ⟨hM₁, 𝓕₁, ⟨e₁⟩⟩ := exists_associatedModule_iso_restrictModuleToSmallEtale B E h S hS p hp
    F₁.val h₁ x
  obtain ⟨hM₂, 𝓕₂, ⟨e₂⟩⟩ := exists_associatedModule_iso_restrictModuleToSmallEtale B E h S hS p hp
    F₂.val h₂ x
  let r := restrictSheafToSmallEtale.{u, v, w, u} B E h S hS p hp x
  let A := SmallEtale.associatedModuleQcoh E (p.obj x).left.1 (contains_base B E h S hS p x)
  let g : A.obj 𝓕₁ ⟶ A.obj 𝓕₂ := e₁.hom ≫ r.map ι ≫ e₂.inv
  have hrι : Mono (r.map ι) := by
    have : PreservesFiniteLimits r :=
      preservesFiniteLimits_restrictSheafToSmallEtale B E h S hS p hp x
    exact Functor.map_mono r ι
  have he₂ : Mono e₂.inv := ⟨fun a b w => by simpa using w =≫ e₂.hom⟩
  have hg : Mono g := mono_comp' inferInstance (mono_comp' hrι he₂)
  let ι₀ : 𝓕₁ ⟶ 𝓕₂ := A.preimage g
  have hι₀ : A.map ι₀ = g := A.map_preimage g
  have hι₀m : Mono ι₀.hom := by
    have hK := (SheafOfModules.isQuasicoherent (p.obj x).left.1.ringCatSheaf).prop_kernel
      ι₀.hom 𝓕₁.property 𝓕₂.property
    let kι : (⟨kernel ι₀.hom, hK⟩ : (SheafOfModules.isQuasicoherent
        (p.obj x).left.1.ringCatSheaf).FullSubcategory) ⟶ 𝓕₁ :=
      ObjectProperty.homMk (kernel.ι ι₀.hom)
    have h0 : kι ≫ ι₀ = 0 := ObjectProperty.hom_ext _ (kernel.condition ι₀.hom)
    have hm : Mono ι₀ := A.mono_of_mono_map (hι₀ ▸ hg)
    have : kι = 0 := (cancel_mono ι₀).1 (h0.trans zero_comp.symm)
    exact Abelian.mono_of_kernel_ι_eq_zero _ (congrArg (fun t => t.hom) this)
  have : Mono (C := (p.obj x).left.1.Modules) ι₀.hom := hι₀m
  have h4 := mono_map_sheafifiedPullbackComparison_associatedModule B E h S hS p hp φ hflat ι₀.hom
  let P := sheafifiedPullbackComparison B E h S hS p hp (etaleTopology B)
    (etaleTopology_le_topology B) φ
  have h5 : Mono (P.map g) := hι₀ ▸ h4
  have h7 : Mono (P.map e₁.hom ≫ P.map (r.map ι) ≫ P.map e₂.inv) := by
    have hc : P.map g = P.map e₁.hom ≫ P.map (r.map ι) ≫ P.map e₂.inv :=
      (P.map_comp _ _).trans (congrArg (P.map e₁.hom ≫ ·) (P.map_comp _ _))
    exact hc ▸ h5
  have h8 : Mono (P.map (r.map ι) ≫ P.map e₂.inv) := by
    have := mono_comp' (inferInstance : Mono (inv (P.map e₁.hom))) h7
    rwa [IsIso.inv_hom_id_assoc] at this
  exact @mono_of_mono _ _ _ _ _ _ (P.map e₂.inv) h8

/-- **The comparison map of sheaves is an isomorphism at a kernel term**: in a short exact
sequence of locally quasi-coherent modules at whose second and third terms it is an isomorphism,
along an arrow over a flat morphism, it is an isomorphism at the first. The inverse image along a
flat morphism keeps the first map a monomorphism
(`AlgebraicGeometry.Stack.mono_map_sheafifiedPullbackComparison_restrict`). -/
theorem isIso_sheafRestrictComparison_app_of_shortExact_of_isIso₂₃
    (hflat : Flat (B.inclusion.map (p.map φ).left))
    {T : ShortComplex (SheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)))} (hT : T.ShortExact)
    (hl₁ : IsLocallyQuasicoherent B E h S hS p hp T.X₁.val)
    (hl₂ : IsLocallyQuasicoherent B E h S hS p hp T.X₂.val)
    (h₂ : IsIso ((sheafRestrictComparison B E h S hS p hp φ).app T.X₂))
    (h₃ : IsIso ((sheafRestrictComparison B E h S hS p hp φ).app T.X₃)) :
    IsIso ((sheafRestrictComparison B E h S hS p hp φ).app T.X₁) := by
  obtain ⟨hPe, _, hR⟩ := exact_epi_shortExact_map_sheafRestrictComparison B E h S hS p hp φ hT
  let ψ := ShortComplex.mapNatTrans T (sheafRestrictComparison B E h S hS p hp φ)
  have := hT.mono_f
  have : Mono (T.map (restrictSheafToSmallEtale.{u, v, w, u} B E h S hS p hp x ⋙
      sheafifiedPullbackComparison B E h S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B) φ)).f :=
    mono_map_sheafifiedPullbackComparison_restrict B E h S hS p hp φ hflat T.f hl₁ hl₂
  have : IsIso ψ.τ₂ := h₂
  have : IsIso ψ.τ₃ := h₃
  exact ShortComplex.isIso₁_of_shortExact_of_isIso₂₃ ψ ⟨hPe⟩ hR

/-- **Local quasi-coherence with the flat base change property passes to the first term** of a
short exact sequence whose first term is locally quasi-coherent and whose other two terms have
it. -/
private theorem isLocallyQuasicoherentWithSheafFlatBaseChange_X₁_of_shortExact
    {T : ShortComplex (SheafOfModules.{u} (ringStructureSheafCore B S hS p hp
      (etaleTopology B) (etaleTopology_le_topology B)))} (hT : T.ShortExact)
    (hl₁ : IsLocallyQuasicoherent B E h S hS p hp T.X₁.val)
    (h₂ : IsLocallyQuasicoherentWithSheafFlatBaseChange B E h S hS p hp T.X₂.val)
    (h₃ : IsLocallyQuasicoherentWithSheafFlatBaseChange B E h S hS p hp T.X₃.val) :
    IsLocallyQuasicoherentWithSheafFlatBaseChange B E h S hS p hp T.X₁.val := by
  have hiff := hasSheafFlatBaseChangeProperty_iff_isIso_sheafRestrictComparison B E h S hS p hp
  exact ⟨hl₁, (hiff _).2 fun φ hφ =>
    isIso_sheafRestrictComparison_app_of_shortExact_of_isIso₂₃ B E h S hS p hp φ hφ hT hl₁ h₂.1
      ((hiff _).1 h₂.2 φ hφ) ((hiff _).1 h₃.2 φ hφ)⟩

/-- **`LQCoh^fbc(𝒪_𝒳)` is a weak Serre subcategory of `Mod(𝒳_ét, 𝒪_𝒳)`** (Stacks 0771 part (2),
the étale half): the étale sheaves of modules which are locally quasi-coherent (**Stacks 06WJ**)
and have the flat base change property (**Stacks 0762**) contain zero and are closed under
isomorphisms, kernels, cokernels and extensions (**Stacks 0754**).

Local quasi-coherence has these closure properties by **Stacks 06WM**. The flat base change
property is invertibility of the natural comparison map of sheaves `c^♯_φ` along arrows over flat
morphisms; its source functor, restriction followed by the inverse image of sheaves of modules,
is right exact, and on monomorphisms between locally quasi-coherent modules also left exact, the
morphism being flat; its target functor is exact. The five lemma then gives each closure
property, the kernel going through the image of the map. -/
theorem isWeakSerreClass_isLocallyQuasicoherentWithSheafFlatBaseChange :
    ObjectProperty.IsWeakSerreClass (fun F : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp
      (etaleTopology B) (etaleTopology_le_topology B)) =>
        IsLocallyQuasicoherentWithSheafFlatBaseChange B E h S hS p hp F.val) := by
  let Q := isLocallyQuasicoherent.{u, v, w, u} B E h S hS p hp
  have hiff := hasSheafFlatBaseChangeProperty_iff_isIso_sheafRestrictComparison B E h S hS p hp
  have hkerQ : Q.IsClosedUnderKernels := isClosedUnderKernels_isLocallyQuasicoherent B E h S hS p hp
  have hcok : ∀ {F₁ F₂ : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B))} {f : F₁ ⟶ F₂} {k : CokernelCofork f} (_ : IsColimit k),
      IsLocallyQuasicoherentWithSheafFlatBaseChange B E h S hS p hp F₁.val →
      IsLocallyQuasicoherentWithSheafFlatBaseChange B E h S hS p hp F₂.val →
      IsLocallyQuasicoherentWithSheafFlatBaseChange B E h S hS p hp k.pt.val :=
    fun hk hF hG => ⟨Q.prop_of_isColimit_cokernelCofork hk hF.1 hG.1, (hiff _).2 fun φ hφ =>
      isIso_sheafRestrictComparison_app_of_isColimit B E h S hS p hp φ hk ((hiff _).1 hF.2 φ hφ)
        ((hiff _).1 hG.2 φ hφ)⟩
  exact
    { exists_zero := by
        obtain ⟨Z, hZ, hZl⟩ := Q.exists_prop_of_containsZero
        exact ⟨Z, hZ, hZl, (hiff Z).2 fun φ _ =>
          isIso_sheafRestrictComparison_app_of_isZero B E h S hS p hp φ hZ⟩
      of_iso := fun e hF => ⟨Q.prop_of_iso e hF.1, hasSheafFlatBaseChangeProperty_of_iso B E h S hS
        p hp _ _ ((SheafOfModules.forget _).mapIso e) hF.2⟩
      cokernels_le := by
        rintro _ ⟨f, k, hk, hF, hG⟩
        exact hcok hk hF hG
      prop_X₂_of_shortExact := fun {T} hT h₁ h₃ =>
        ⟨(isLocallyQuasicoherent_twoOutOfThree B E h S hS p hp T hT).2.2 h₁.1 h₃.1,
          (hiff _).2 fun φ _ => isIso_sheafRestrictComparison_app_of_shortExact B E h S hS p hp φ
            hT ((hiff _).1 h₁.2 φ ‹_›) ((hiff _).1 h₃.2 φ ‹_›)⟩
      kernels_le := by
        rintro _ ⟨f, k, hk, hF, hG⟩
        have hC := hcok (cokernelIsCokernel f) hF hG
        have hIl : IsLocallyQuasicoherent B E h S hS p hp (Abelian.image f).val :=
          Q.prop_kernel (cokernel.π f) hG.1 hC.1
        let Sb := ShortComplex.mk (Abelian.image.ι f) (cokernel.π f) (by simp)
        have hSb : Sb.ShortExact :=
          { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel (cokernel.π f)) }
        have hI := isLocallyQuasicoherentWithSheafFlatBaseChange_X₁_of_shortExact B E h S hS p hp
          hSb hIl hG hC
        let Sa := ShortComplex.mk k.ι (Abelian.factorThruImage f) (by
          rw [← cancel_mono (Abelian.image.ι f), Category.assoc, Abelian.image.fac,
            KernelFork.condition, zero_comp])
        have hSa : Sa.ShortExact :=
          { exact := ShortComplex.exact_of_f_is_kernel _
              (isKernelOfComp (Abelian.image.ι f) f hk Sa.zero (Abelian.image.fac f))
            mono_f := Fork.IsLimit.mono hk }
        exact isLocallyQuasicoherentWithSheafFlatBaseChange_X₁_of_shortExact B E h S hS p hp hSa
          (Q.prop_of_isLimit_kernelFork hk hF.1 hG.1) hF hI }

end Closure

/-- **Stacks 0771, part (2), the étale half: `LQCoh^fbc(𝒪_𝒳)` is a weak Serre subcategory of
`Mod(𝒳_ét, 𝒪_𝒳)`**, for an algebraic stack `𝒳`, at module universe `u`, with the abelian
structure coming from the sheafification of abelian presheaves on the associated étale site
(`AlgebraicGeometry.Stack.hasSheafify_etaleAssociatedTopology`). -/
@[stacks 0771 "part (2), the étale half: LQCoh^fbc is a weak Serre subcategory of \
  Mod(𝒳_ét, 𝒪_𝒳), with the flat base change property of 0762 read on sheaves"]
theorem isWeakSerreClass_lqcohSheafFbcEtaleModules (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    letI := hasSheafify_etaleAssociatedTopology B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
    letI := wEqualsLocallyBijective_etaleAssociatedTopology B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids
    (lqcohSheafFbcEtaleModules.{u, w, u} B E h S hS 𝒳).IsWeakSerreClass :=
  let := hasSheafify_etaleAssociatedTopology B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
  let := wEqualsLocallyBijective_etaleAssociatedTopology B S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids
  isWeakSerreClass_isLocallyQuasicoherentWithSheafFlatBaseChange B E h S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids

end AlgebraicGeometry.Stack

end
