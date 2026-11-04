module

public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.CategoryTheory.Localization.Adjunction
public import StacksFrontier.CategoryTheory.FiberedCategory.Amelioration
public import StacksFrontier.CategoryTheory.Sites.Cocontinuous.CocontinuousComp
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.DerivedLowerShriekFibreHomologyIso
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.DerivedLowerShriekFunctoriality
public import StacksFrontier.CategoryTheory.Sites.Localization.PushforwardAdjunction
import StacksCore.Tactic.StacksAttribute

/-!
# Derived lower shriek of a morphism of fibred categories, through the amelioration

Let `u : C' ⥤ C` be a 1-morphism of fibred categories over a ringed site `(D, O_D)` and let `Lg_!`
be the left derived lower-shriek functor of the induced morphism of topoi `g : Sh(C') ⟶ Sh(C)`.
This file shows that `L_n g_!(F')` is the sheaf associated to the presheaf `U ↦ H_n(I_U, F'_U)`,
where `I_U` is the category of pairs `(U', φ : U ⟶ u U')` with `p(φ)` the identity.

The functor `u` factors as `C' ⥤ C'' ⥤ C` through the amelioration `C''`, whose projection `u''`
makes it a fibred category over `C` with fibre `I_U` over `U`, and whose inclusion `u'` has a left
adjoint `w` (the retraction). On abelian sheaves `g'_!` is restriction along `w`, and
`Lg_! = Lg''_! ∘ g'_!`.

## Main definitions

* `Stacks.Sites.FibredCategory.MorphismSituation.amelioratedSituation`: the amelioration of `u`,
  as a fibred category over the total category with its inherited topology and the structure
  sheaf `O_C = π⁻¹O_D`.
* `Stacks.Sites.FibredCategory.MorphismSituation.amelioratedLowerShriek`: `g'_!`, restriction of
  abelian sheaves along the retraction of the amelioration.

## Main results

* `CategoryTheory.Functor.inheritedTopology_comp`: the topology inherited along a composite of
  fibred categories is inherited in two steps.
* `Stacks.Sites.FibredCategory.MorphismSituation.amelioratedTopology_eq`: the topology the
  amelioration inherits from the total category is the one it inherits from the base.
* `Stacks.Sites.FibredCategory.MorphismSituation.derivedAbelianLowerShriekAmelioratedCompIso`:
  the factorization `Lg_! = Lg''_! ∘ g'_!`.
* `MorphismSituation.derivedAbelianLowerShriekHomologyAmelioratedObjIso`:
  `L_n g_!(F')` is `L_n g''_!(g'_!F')`.
* `MorphismSituation.derivedAbelianLowerShriekHomologyObjIsoFiberHomologySheaf`:
  for an abelian sheaf `F'` on the source, `L_n g_!(F')` is the sheaf on the total category
  associated to the presheaf `U ↦ H_n(I_U, F'_U)`, where `F'_U` is `(U', φ) ↦ F'(U')`. It takes
  as hypotheses the acyclicity conditions for `g_!` and for `g''_!` and the cover acyclicity of
  the amelioration.

## References

* [Stacks Project, Tag 08PK](https://stacks.math.columbia.edu/tag/08PK)
* [Stacks Project, Tag 08PJ](https://stacks.math.columbia.edu/tag/08PJ)
* [Stacks Project, Tag 08PA](https://stacks.math.columbia.edu/tag/08PA)
* [Stacks Project, Tag 08NF](https://stacks.math.columbia.edu/tag/08NF)
* [Stacks Project, Tag 08P3](https://stacks.math.columbia.edu/tag/08P3)
* [Stacks Project, Tag 06NW](https://stacks.math.columbia.edu/tag/06NW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

universe v₁ v₂ v₃ u₁ u₂ u₃

/-- If `i ⋙ q` is cocontinuous, the pullback along `i` of a sieve covering for the topology
inherited along `q` is covering. -/
private theorem functorPullback_mem_of_mem_inheritedTopology {𝒜 : Type u₁} [Category.{v₁} 𝒜]
    {ℰ : Type u₂} [Category.{v₂} ℰ] {ℬ : Type u₃} [Category.{v₃} ℬ]
    (i : 𝒜 ⥤ ℰ) (q : ℰ ⥤ ℬ) (J : GrothendieckTopology 𝒜) (K : GrothendieckTopology ℬ)
    [(i ⋙ q).IsCocontinuous J K] : ∀ (X : ℰ) (R : Sieve X), R ∈ q.inheritedTopology K X →
    ∀ (Y : 𝒜) (f : i.obj Y ⟶ X), (R.pullback f).functorPullback i ∈ J Y := by
  intro X R hR
  induction hR with
  | of X R₀ hR₀ =>
    intro Y f
    have hcart : ∀ ⦃Z : ℰ⦄ (g : Z ⟶ X), R₀ g → q.IsStronglyCartesian (q.map g) g :=
      fun _ g hg ↦ hR₀.1 g hg
    have hcov : (Sieve.generate (R₀.map q)).pullback (q.map f) ∈ K ((i ⋙ q).obj Y) :=
      K.pullback_stable (q.map f) ((GrothendieckTopology.mem_toPrecoverage_iff ..).mp hR₀.2)
    refine J.superset_covering ?_ ((i ⋙ q).cover_lift J K hcov)
    intro Z a ha
    refine (generate_arrows_map_iff q R₀ hcart (i.map a ≫ f)).mpr ?_
    have ha' : (Sieve.generate (R₀.map q)).arrows ((i ⋙ q).map a ≫ q.map f) := ha
    simpa only [q.map_comp, Functor.comp_map] using ha'
  | top X => intro Y f; simp
  | pullback X R _ X' g ih =>
    intro Y f
    simpa only [Sieve.pullback_comp] using ih Y (f ≫ g)
  | transitive X R T _ _ ih ihT =>
    intro Y f
    refine J.transitive (ih Y f) _ ?_
    intro Z a ha
    have hsieve : (T.pullback (i.map a ≫ f)).functorPullback i =
        ((T.pullback f).functorPullback i).pullback a := by
      refine Sieve.ext fun W h ↦ ?_
      change T.arrows (i.map h ≫ i.map a ≫ f) ↔ T.arrows (i.map (h ≫ a) ≫ f)
      rw [i.map_comp, Category.assoc]
    rw [← hsieve]
    simpa using ihT (f := i.map a ≫ f) ha Z (𝟙 _)

/-- The topology inherited from a topology `K` on the base along a functor `q` is coarser than
every topology for which `q` is cocontinuous. -/
theorem inheritedTopology_le_of_isCocontinuous {𝒜 : Type u₁} [Category.{v₁} 𝒜]
    {ℬ : Type u₂} [Category.{v₂} ℬ] (q : 𝒜 ⥤ ℬ) (J : GrothendieckTopology 𝒜)
    (K : GrothendieckTopology ℬ) [q.IsCocontinuous J K] :
    q.inheritedTopology K ≤ J := by
  intro X R hR
  have : (𝟭 𝒜 ⋙ q).IsCocontinuous J K := inferInstanceAs (q.IsCocontinuous J K)
  simpa using functorPullback_mem_of_mem_inheritedTopology (𝟭 𝒜) q J K X R hR X (𝟙 _)

/-- A functor `i` whose composite with `q` is cocontinuous is cocontinuous for the topology
inherited along `q`. -/
theorem isCocontinuous_inheritedTopology_of_comp {𝒜 : Type u₁} [Category.{v₁} 𝒜]
    {ℰ : Type u₂} [Category.{v₂} ℰ] {ℬ : Type u₃} [Category.{v₃} ℬ]
    (i : 𝒜 ⥤ ℰ) (q : ℰ ⥤ ℬ) (J : GrothendieckTopology 𝒜) (K : GrothendieckTopology ℬ)
    [(i ⋙ q).IsCocontinuous J K] :
    i.IsCocontinuous J (q.inheritedTopology K) := by
  constructor
  intro X R hR
  simpa using functorPullback_mem_of_mem_inheritedTopology i q J K _ R hR X (𝟙 _)

/-- The topology inherited along a composite of fibred categories is inherited in two steps. -/
theorem inheritedTopology_comp {𝒜 : Type u₁} [Category.{v₁} 𝒜] {ℰ : Type u₂} [Category.{v₂} ℰ]
    {ℬ : Type u₃} [Category.{v₃} ℬ] (i : 𝒜 ⥤ ℰ) (q : ℰ ⥤ ℬ) [i.IsFibered] [q.IsFibered]
    [(i ⋙ q).IsFibered] (K : GrothendieckTopology ℬ) :
    (i ⋙ q).inheritedTopology K = i.inheritedTopology (q.inheritedTopology K) := by
  have hq : q.IsCocontinuous (q.inheritedTopology K) K :=
    Stacks.Sites.FibredCategory.isCocontinuous_inheritedTopology_of_isFibered q K
  have hi : i.IsCocontinuous (i.inheritedTopology (q.inheritedTopology K))
      (q.inheritedTopology K) :=
    Stacks.Sites.FibredCategory.isCocontinuous_inheritedTopology_of_isFibered i
      (q.inheritedTopology K)
  have : (i ⋙ q).IsCocontinuous (i.inheritedTopology (q.inheritedTopology K)) K :=
    isCocontinuous_comp i q _ (q.inheritedTopology K)
  have : (i ⋙ q).IsCocontinuous ((i ⋙ q).inheritedTopology K) K :=
    Stacks.Sites.FibredCategory.isCocontinuous_inheritedTopology_of_isFibered (i ⋙ q) K
  refine le_antisymm (inheritedTopology_le_of_isCocontinuous (i ⋙ q) _ K) ?_
  have := isCocontinuous_inheritedTopology_of_comp i q ((i ⋙ q).inheritedTopology K) K
  exact inheritedTopology_le_of_isCocontinuous i _ (q.inheritedTopology K)

end CategoryTheory.Functor

namespace Stacks.Sites.FibredCategory

section Helpers

attribute [local instance] HasDerivedCategory.standard

/-- An adjunction of additive functors, applied degreewise to complexes: the unit and counit are
the degreewise ones. -/
def adjunctionMapHomologicalComplex {A B : Type*} [Category A] [Abelian A] [Category B]
    [Abelian B] {F : A ⥤ B} {G : B ⥤ A} [F.Additive] [G.Additive] (adj : F ⊣ G)
    {ι : Type*} (c : ComplexShape ι) :
    F.mapHomologicalComplex c ⊣ G.mapHomologicalComplex c :=
  Adjunction.mkOfUnitCounit
    { unit := NatTrans.mapHomologicalComplex adj.unit c
      counit := NatTrans.mapHomologicalComplex adj.counit c
      left_triangle := by ext X i; simp
      right_triangle := by ext X i; simp }

/-- An adjunction of exact functors of abelian categories descends to an adjunction of the
functors it induces on the unbounded derived categories. -/
def adjunctionMapDerivedCategory {A : Type*} [Category A] [Abelian A]
    [HasDerivedCategory A] {B : Type*} [Category B] [Abelian B] [HasDerivedCategory B]
    {F : A ⥤ B} {G : B ⥤ A} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (adj : F ⊣ G) :
    F.mapDerivedCategory ⊣ G.mapDerivedCategory :=
  letI : CatCommSq (F.mapHomologicalComplex (ComplexShape.up ℤ)) DerivedCategory.Q
      DerivedCategory.Q F.mapDerivedCategory := ⟨F.mapDerivedCategoryFactors.symm⟩
  letI : CatCommSq (G.mapHomologicalComplex (ComplexShape.up ℤ)) DerivedCategory.Q
      DerivedCategory.Q G.mapDerivedCategory := ⟨G.mapDerivedCategoryFactors.symm⟩
  (adjunctionMapHomologicalComplex adj (ComplexShape.up ℤ)).localization
    DerivedCategory.Q (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))
    DerivedCategory.Q (HomologicalComplex.quasiIso B (ComplexShape.up ℤ)) _ _


end Helpers

namespace MorphismSituation

universe u₀ u₁ u₂ v₀ v₁ v₂ w

variable (S : MorphismSituation.{u₀, u₁, u₂, v₀, v₁, v₂, max w u₀ u₁ u₂ v₀ v₁ v₂})

/-- `O_C = π⁻¹O_D`, the structure sheaf of the total category: restriction of the base structure
sheaf along the projection. -/
abbrev totalStructureSheaf : Sheaf S.totalTopology CommRingCat.{max w u₀ u₁ u₂ v₀ v₁ v₂} :=
  (S.p.sheafPushforwardContinuous CommRingCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}
    S.totalTopology S.base.J).obj S.base.O

/-- The total category of the situation as a ringed site: the inherited topology together with
the structure sheaf `O_C = π⁻¹O_D`. -/
abbrev totalRingedSite : AlgebraicGeometry.RingedSite.{u₁, v₁, max w u₀ u₁ u₂ v₀ v₁ v₂} where
  C := S.total
  J := S.totalTopology
  O := S.totalStructureSheaf

/-- The amelioration `C''` of the 1-morphism `u`: its objects are the triples
`(x, y, f : y ⟶ u x)` with `x` in `C'`, `y` in `C` over the same object of the base and `f` lying
over the identity. -/
abbrev amelioration :=
  CategoryTheory.Amelioration S.p' S.p S.u S.isFibredOneMorphism.comp_eq

/-- The amelioration of `u`, with its objects and morphisms placed in one universe, so that the
fibres of its projection are small categories. -/
abbrev amelioratedTotal := AsSmall.{max u₁ u₂ v₁ v₂} (amelioration S)

/-- The projection `u'' : C'' ⥤ C` of the amelioration, `(x, y, f) ↦ y`. -/
abbrev amelioratedProjection : amelioratedTotal S ⥤ S.total :=
  AsSmall.down ⋙ CategoryTheory.Amelioration.proj S.p' S.p S.u S.isFibredOneMorphism.comp_eq

/-- The retraction `w : C'' ⥤ C'` of the amelioration, `(x, y, f) ↦ x`. -/
abbrev amelioratedRetraction : amelioratedTotal S ⥤ S.source :=
  AsSmall.down ⋙ CategoryTheory.Amelioration.retract S.p' S.p S.u S.isFibredOneMorphism.comp_eq

/-- The inclusion `u' : C' ⥤ C''` of the amelioration, `x ↦ (x, u x, id)`. -/
abbrev amelioratedInclusion : S.source ⥤ amelioratedTotal S :=
  CategoryTheory.Amelioration.incl S.p' S.p S.u S.isFibredOneMorphism.comp_eq ⋙ AsSmall.up

/-- The structure functor `C'' ⥤ D` of the amelioration over the base. -/
abbrev amelioratedStructure : amelioratedTotal S ⥤ S.base.C :=
  AsSmall.down ⋙
    CategoryTheory.Amelioration.structureFunctor S.p' S.p S.u S.isFibredOneMorphism.comp_eq

/-- The structure functor of the amelioration over the base is its projection to the total
category followed by the projection of the total category. -/
theorem amelioratedStructure_eq : amelioratedStructure S = amelioratedProjection S ⋙ S.p := by
  dsimp only [amelioratedStructure, amelioratedProjection]
  rw [Functor.assoc, CategoryTheory.Amelioration.structureFunctor_eq]

/-- The projection of the amelioration makes it a fibred category over the total category. -/
instance amelioratedProjection_isFibered : (amelioratedProjection S).IsFibered :=
  letI : (CategoryTheory.Amelioration.proj S.p' S.p S.u
      S.isFibredOneMorphism.comp_eq).IsFibered :=
    CategoryTheory.Amelioration.proj_isFibered (hFq := S.isFibredOneMorphism.comp_eq)
      S.isFibredOneMorphism
  CategoryTheory.Functor.IsFibered.comp_equivalence_inverse
    (AsSmall.equiv (C := amelioration S))
    (CategoryTheory.Amelioration.proj S.p' S.p S.u S.isFibredOneMorphism.comp_eq)
    rfl fun _ => rfl

/-- The structure functor of the amelioration over the base is a fibred category. -/
instance amelioratedStructure_isFibered : (amelioratedStructure S).IsFibered :=
  letI : (CategoryTheory.Amelioration.structureFunctor S.p' S.p S.u
      S.isFibredOneMorphism.comp_eq).IsFibered :=
    CategoryTheory.Amelioration.structureFunctor_isFibered S.isFibredOneMorphism
  CategoryTheory.Functor.IsFibered.comp_equivalence_inverse
    (AsSmall.equiv (C := amelioration S))
    (CategoryTheory.Amelioration.structureFunctor S.p' S.p S.u S.isFibredOneMorphism.comp_eq)
    rfl fun _ => rfl

/-- The composite of the projection of the amelioration with the structure functor of the
total category is a fibred category. -/
instance amelioratedProjectionComp_isFibered : (amelioratedProjection S ⋙ S.p).IsFibered := by
  rw [← amelioratedStructure_eq]
  infer_instance

/-- The topology the amelioration inherits from the total category is the one it inherits from
the base. -/
theorem amelioratedTopology_eq :
    (amelioratedProjection S).inheritedTopology S.totalTopology =
      (amelioratedStructure S).inheritedTopology S.base.J := by
  rw [amelioratedStructure_eq, Functor.inheritedTopology_comp (amelioratedProjection S) S.p]

/-- **The ameliorated situation.** The amelioration of `u`, as a fibred category over the total
category with its inherited topology and the structure sheaf `O_C = π⁻¹O_D`; its fibre over `U`
is the category `I_U` of pairs `(U', U ⟶ u U')` over the identity of `p(U)`. -/
abbrev amelioratedSituation :
    FibredCategorySituation.{u₁, v₁, max u₁ u₂ v₁ v₂, max u₁ u₂ v₁ v₂,
      max w u₀ u₁ u₂ v₀ v₁ v₂} where
  base := totalRingedSite S
  C := amelioratedTotal S
  p := amelioratedProjection S

/-- The retraction of the amelioration is a 1-morphism of fibred categories over the base, from
the amelioration to the source. -/
theorem amelioratedRetraction_isFibredOneMorphism :
    (amelioratedStructure S).IsFibredOneMorphism S.p' (amelioratedRetraction S) where
  comp_eq := rfl
  map_isStronglyCartesian := by
    intro _ _ f _ _ φ h
    refine (CategoryTheory.Amelioration.retract_isFibredOneMorphism
        (hFq := S.isFibredOneMorphism.comp_eq) S.isFibredOneMorphism).map_isStronglyCartesian f
      (AsSmall.down.map φ) ?_
    exact (AsSmall.equiv (C := amelioration S)).symm.isStronglyCartesian_map_functor
      (CategoryTheory.Amelioration.structureFunctor S.p' S.p S.u
        S.isFibredOneMorphism.comp_eq) rfl f φ h

/-- The inclusion of the amelioration is a 1-morphism of fibred categories over the base, from
the source to the amelioration. -/
theorem amelioratedInclusion_isFibredOneMorphism :
    S.p'.IsFibredOneMorphism (amelioratedStructure S) (amelioratedInclusion S) where
  comp_eq :=
    (CategoryTheory.Amelioration.incl_isFibredOneMorphism
      (hFq := S.isFibredOneMorphism.comp_eq)).comp_eq
  map_isStronglyCartesian := by
    intro _ _ f _ _ φ h
    exact (AsSmall.equiv (C := amelioration S)).isStronglyCartesian_map_functor
      (amelioratedStructure S) rfl f _
      ((CategoryTheory.Amelioration.incl_isFibredOneMorphism
        (hFq := S.isFibredOneMorphism.comp_eq)).map_isStronglyCartesian f φ h)

/-- The inclusion of the amelioration is continuous for the topologies the source and the
amelioration inherit from the base. -/
instance amelioratedInclusion_isContinuous :
    (amelioratedInclusion S).IsContinuous S.sourceTopology (amelioratedSituation S).topology := by
  have h := CategoryTheory.Functor.IsFibredOneMorphism.isContinuous_inheritedTopology
    (p := amelioratedStructure S) (u := amelioratedInclusion S) S.base.J
    (amelioratedInclusion_isFibredOneMorphism S)
  rw [← amelioratedTopology_eq] at h
  exact h

/-- The inclusion of the amelioration is cocontinuous for the topologies the source and the
amelioration inherit from the base. -/
instance amelioratedInclusion_isCocontinuous :
    (amelioratedInclusion S).IsCocontinuous S.sourceTopology
      (amelioratedSituation S).topology := by
  have h := CategoryTheory.Functor.IsFibredOneMorphism.isCocontinuous_inheritedTopology
    (p := amelioratedStructure S) (u := amelioratedInclusion S) S.base.J
    (amelioratedInclusion_isFibredOneMorphism S)
  rw [← amelioratedTopology_eq] at h
  exact h

/-- The retraction of the amelioration is continuous for the topologies the amelioration and the
source inherit from the base. -/
instance amelioratedRetraction_isContinuous :
    (amelioratedRetraction S).IsContinuous (amelioratedSituation S).topology
      S.sourceTopology := by
  have h := CategoryTheory.Functor.IsFibredOneMorphism.isContinuous_inheritedTopology
    (p := S.p') (u := amelioratedRetraction S) S.base.J
    (amelioratedRetraction_isFibredOneMorphism S)
  rw [← amelioratedTopology_eq] at h
  exact h

/-- The retraction of the amelioration is cocontinuous for the topologies the amelioration and
the source inherit from the base. -/
instance amelioratedRetraction_isCocontinuous :
    (amelioratedRetraction S).IsCocontinuous (amelioratedSituation S).topology
      S.sourceTopology := by
  have h := CategoryTheory.Functor.IsFibredOneMorphism.isCocontinuous_inheritedTopology
    (p := S.p') (u := amelioratedRetraction S) S.base.J
    (amelioratedRetraction_isFibredOneMorphism S)
  rw [← amelioratedTopology_eq] at h
  exact h

/-- The retraction of the amelioration is left adjoint to its inclusion. -/
def amelioratedAdjunction : amelioratedRetraction S ⊣ amelioratedInclusion S :=
  (AsSmall.equiv (C := amelioration S)).symm.toAdjunction.comp
    CategoryTheory.Amelioration.retractAdjIncl

/-- The 1-morphism `u` is the inclusion of the amelioration followed by its projection. -/
theorem amelioratedInclusion_comp_amelioratedProjection :
    amelioratedInclusion S ⋙ amelioratedProjection S = S.u :=
  (CategoryTheory.Amelioration.incl_comp_proj
    (hFq := S.isFibredOneMorphism.comp_eq)).symm

/-- `(g')⁻¹ : Ab(C'') ⥤ Ab(C')`, restriction of abelian sheaves along the inclusion of the
amelioration. -/
abbrev amelioratedInverseImage :
    Sheaf (amelioratedSituation S).topology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂} ⥤
      Sheaf S.sourceTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂} :=
  (amelioratedInclusion S).sheafPushforwardContinuous
    AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂} S.sourceTopology (amelioratedSituation S).topology

/-- `g'_! : Ab(C') ⥤ Ab(C'')`, restriction of abelian sheaves along the retraction of the
amelioration. -/
abbrev amelioratedLowerShriek :
    Sheaf S.sourceTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂} ⥤
      Sheaf (amelioratedSituation S).topology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂} :=
  (amelioratedRetraction S).sheafPushforwardContinuous
    AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂} (amelioratedSituation S).topology S.sourceTopology

/-- Restriction of abelian sheaves along the retraction of the amelioration is left adjoint to
restriction along the inclusion. -/
def amelioratedLowerShriekAdjunction :
    amelioratedLowerShriek S ⊣ amelioratedInverseImage S :=
  (amelioratedAdjunction S).sheafPushforwardAdjunction
    AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}

/-- The projection of the amelioration is continuous for the inherited topologies. -/
instance amelioratedProjection_isContinuous :
    (amelioratedProjection S).IsContinuous (amelioratedSituation S).topology S.totalTopology :=
  (amelioratedSituation S).isContinuous

/-- The projection of the amelioration is cocontinuous for the inherited topologies. -/
instance amelioratedProjection_isCocontinuous :
    (amelioratedProjection S).IsCocontinuous (amelioratedSituation S).topology S.totalTopology :=
  (amelioratedSituation S).isCocontinuous

/-- The underlying presheaf of `g'_!F'` assigns to an object `(U', φ)` of the amelioration the
value `F'(U')` of the coefficient sheaf at its source component. -/
theorem amelioratedLowerShriek_obj_obj
    (F' : Sheaf S.sourceTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}) :
    ((amelioratedLowerShriek S).obj F').obj = (amelioratedRetraction S).op ⋙ F'.obj := rfl

/-- Restriction of abelian sheaves from the total category to the source is restriction along the
projection of the amelioration followed by restriction along its inclusion. -/
def amelioratedInverseImageCompIso :
    (amelioratedSituation S).abelianInverseImage ⋙ amelioratedInverseImage S ≅
      S.abelianInverseImage :=
  Functor.sheafPushforwardContinuousComp'
    (eqToIso (amelioratedInclusion_comp_amelioratedProjection S))
    AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂} S.sourceTopology (amelioratedSituation S).topology
    S.totalTopology

section Derived

attribute [local instance] HasDerivedCategory.standard

variable [HasSheafify (amelioratedSituation S).topology
    AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}]
  [(amelioratedLowerShriek S).IsRightAdjoint]
  [(amelioratedInverseImage S).IsRightAdjoint]
  [∀ F : (amelioratedTotal S)ᵒᵖ ⥤ AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂},
    (amelioratedRetraction S).op.HasPointwiseRightKanExtension F]
  [∀ F : S.sourceᵒᵖ ⥤ AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂},
    (amelioratedInclusion S).op.HasPointwiseRightKanExtension F]
  [(amelioratedSituation S).abelianInverseImage.IsRightAdjoint]
  [∀ F : (amelioratedTotal S)ᵒᵖ ⥤ AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂},
    (amelioratedProjection S).op.HasPointwiseRightKanExtension F]

/-- Restriction of abelian sheaves along the projection of the amelioration is additive. -/
instance amelioratedBaseInverseImage_additive :
    (amelioratedSituation S).abelianInverseImage.Additive :=
  Stacks.Cohomology.DerivedLowerShriek.additive_abelianRestriction.{max w u₀ u₁ u₂ v₀ v₁ v₂,
    max u₁ u₂ v₁ v₂, max u₁ u₂ v₁ v₂, v₁, u₁} (amelioratedSituation S).topology S.totalTopology
    (amelioratedProjection S)

/-- Restriction of abelian sheaves along the projection of the amelioration preserves finite
colimits. -/
instance amelioratedBaseInverseImage_preservesFiniteColimits :
    PreservesFiniteColimits (amelioratedSituation S).abelianInverseImage :=
  Stacks.Cohomology.DerivedLowerShriek.preservesFiniteColimits_abelianRestriction.{max w u₀ u₁ u₂
    v₀ v₁ v₂, max u₁ u₂ v₁ v₂, max u₁ u₂ v₁ v₂, v₁, u₁} (amelioratedSituation S).topology
    S.totalTopology (amelioratedProjection S)

/-- Restriction of abelian sheaves along the projection of the amelioration preserves finite
limits. -/
instance amelioratedBaseInverseImage_preservesFiniteLimits :
    PreservesFiniteLimits (amelioratedSituation S).abelianInverseImage := inferInstance

/-- Restriction of abelian sheaves along the retraction of the amelioration is additive. -/
instance amelioratedLowerShriek_additive : (amelioratedLowerShriek S).Additive :=
  Stacks.Cohomology.DerivedLowerShriek.additive_abelianRestriction.{max w u₀ u₁ u₂ v₀ v₁ v₂,
    max u₁ u₂ v₁ v₂, max u₁ u₂ v₁ v₂, v₂, u₂} (amelioratedSituation S).topology S.sourceTopology
    (amelioratedRetraction S)

/-- Restriction of abelian sheaves along the retraction of the amelioration preserves finite
colimits. -/
instance amelioratedLowerShriek_preservesFiniteColimits :
    PreservesFiniteColimits (amelioratedLowerShriek S) :=
  Stacks.Cohomology.DerivedLowerShriek.preservesFiniteColimits_abelianRestriction.{max w u₀ u₁ u₂
    v₀ v₁ v₂, max u₁ u₂ v₁ v₂, max u₁ u₂ v₁ v₂, v₂, u₂} (amelioratedSituation S).topology
    S.sourceTopology (amelioratedRetraction S)

/-- Restriction of abelian sheaves along the retraction of the amelioration preserves finite
limits. -/
instance amelioratedLowerShriek_preservesFiniteLimits :
    PreservesFiniteLimits (amelioratedLowerShriek S) := inferInstance

/-- Restriction of abelian sheaves along the inclusion of the amelioration is additive. -/
instance amelioratedInverseImage_additive : (amelioratedInverseImage S).Additive :=
  Stacks.Cohomology.DerivedLowerShriek.additive_abelianRestriction.{max w u₀ u₁ u₂ v₀ v₁ v₂,
    v₂, u₂, max u₁ u₂ v₁ v₂, max u₁ u₂ v₁ v₂} S.sourceTopology (amelioratedSituation S).topology
    (amelioratedInclusion S)

/-- Restriction of abelian sheaves along the inclusion of the amelioration preserves finite
colimits. -/
instance amelioratedInverseImage_preservesFiniteColimits :
    PreservesFiniteColimits (amelioratedInverseImage S) :=
  Stacks.Cohomology.DerivedLowerShriek.preservesFiniteColimits_abelianRestriction.{max w u₀ u₁ u₂
    v₀ v₁ v₂, v₂, u₂, max u₁ u₂ v₁ v₂, max u₁ u₂ v₁ v₂} S.sourceTopology
    (amelioratedSituation S).topology (amelioratedInclusion S)

/-- Restriction of abelian sheaves along the inclusion of the amelioration preserves finite
limits. -/
instance amelioratedInverseImage_preservesFiniteLimits :
    PreservesFiniteLimits (amelioratedInverseImage S) := inferInstance

/-- `g'_!` on the unbounded derived categories, induced degreewise. -/
abbrev derivedAmelioratedLowerShriek :
    DerivedCategory (Sheaf S.sourceTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}) ⥤
      DerivedCategory (Sheaf (amelioratedSituation S).topology
        AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}) :=
  (amelioratedLowerShriek S).mapDerivedCategory

/-- `(g')⁻¹` on the unbounded derived categories, induced degreewise. -/
abbrev derivedAmelioratedInverseImage :
    DerivedCategory (Sheaf (amelioratedSituation S).topology
        AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}) ⥤
      DerivedCategory (Sheaf S.sourceTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}) :=
  (amelioratedInverseImage S).mapDerivedCategory

/-- The adjunction `Lg'_! ⊣ (g')⁻¹` on the unbounded derived categories. -/
def derivedAmelioratedLowerShriekAdjunction :
    derivedAmelioratedLowerShriek S ⊣ derivedAmelioratedInverseImage S :=
  adjunctionMapDerivedCategory (amelioratedLowerShriekAdjunction S)

/-- The factorization of restriction of abelian sheaves through the amelioration, on the
unbounded derived categories. -/
def derivedAmelioratedInverseImageCompIso :
    (amelioratedSituation S).derivedAbelianInverseImage ⋙ derivedAmelioratedInverseImage S ≅
      S.derivedAbelianInverseImage :=
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (Sheaf S.totalTopology
      AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}) (ComplexShape.up ℤ))
    (((amelioratedSituation S).abelianInverseImage.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q) ⋙ derivedAmelioratedInverseImage S)
    (S.abelianInverseImage.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    _ _
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (amelioratedInverseImage S).mapDerivedCategoryFactors ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (Functor.mapHomologicalComplexCompIso (amelioratedInverseImageCompIso S)
          (ComplexShape.up ℤ)) DerivedCategory.Q)

variable [(S.abelianLowerShriekOnHomotopy ⋙ DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
    (HomotopyCategory.quasiIso (Sheaf S.sourceTopology
      AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}) (ComplexShape.up ℤ))]
  [(((amelioratedSituation S).abelianLowerShriekOnHomotopy ⋙
      DerivedCategory.Qh)).HasPointwiseLeftDerivedFunctor
    (HomotopyCategory.quasiIso (Sheaf (amelioratedSituation S).topology
      AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}) (ComplexShape.up ℤ))]

/-- **The derived lower shriek of `u` factors through the amelioration.** Given the acyclicity
hypotheses `h` for `g_!` and `h''` for `g''_!`, `Lg_! = Lg''_! ∘ g'_!`, with `g'_!` restriction
along the retraction. -/
def derivedAbelianLowerShriekAmelioratedCompIso (h : S.AbelianLowerShriekAcyclic)
    (h'' : (amelioratedSituation S).AbelianLowerShriekAcyclic) :
    derivedAmelioratedLowerShriek S ⋙ (amelioratedSituation S).derivedAbelianLowerShriek ≅
      S.derivedAbelianLowerShriek :=
  Adjunction.leftAdjointCompIso (derivedAmelioratedLowerShriekAdjunction S)
    ((amelioratedSituation S).derivedAbelianLowerShriekAdjunction h'')
    (S.derivedAbelianLowerShriekAdjunction h)
    (derivedAmelioratedInverseImageCompIso S)

/-- `F' ↦ H^{-n}(Lg_! F')`, the `n`th derived lower shriek of an abelian sheaf on the source
placed in degree zero. -/
abbrev derivedAbelianLowerShriekHomology (n : ℕ) :
    Sheaf S.sourceTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂} ⥤
      Sheaf S.totalTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂} :=
  DerivedCategory.singleFunctor (Sheaf S.sourceTopology
      AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}) 0 ⋙
    S.derivedAbelianLowerShriek ⋙
      DerivedCategory.homologyFunctor (Sheaf S.totalTopology
        AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}) (-(n : ℤ))

/-- The `n`th derived lower shriek of `F'` along `u` is the `n`th derived lower shriek of
`g'_!F'` along the projection of the amelioration, given the acyclicity hypotheses `h` for `g_!`
and `h''` for `g''_!`. -/
def derivedAbelianLowerShriekHomologyAmelioratedObjIso (h : S.AbelianLowerShriekAcyclic)
    (h'' : (amelioratedSituation S).AbelianLowerShriekAcyclic) (n : ℕ)
    (F' : Sheaf S.sourceTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}) :
    (S.derivedAbelianLowerShriekHomology n).obj F' ≅
      ((amelioratedSituation S).derivedAbelianLowerShriekHomology n).obj
        ((amelioratedLowerShriek S).obj F') :=
  (DerivedCategory.homologyFunctor _ (-(n : ℤ))).mapIso
      ((S.derivedAbelianLowerShriekAmelioratedCompIso h h'').symm.app
        ((DerivedCategory.singleFunctor (Sheaf S.sourceTopology
          AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}) 0).obj F')) ≪≫
    (DerivedCategory.homologyFunctor _ (-(n : ℤ))).mapIso
      ((amelioratedSituation S).derivedAbelianLowerShriek.mapIso
        (((amelioratedLowerShriek S).mapDerivedCategorySingleFunctor 0).app F'))

/-- For an abelian sheaf `F'` on the source, `L_n g_!(F')` is the sheaf on the total category
associated to the presheaf `U ↦ H_n(I_U, F'_U)`. This takes as hypotheses the acyclicity
conditions `h` for `g_!` and `h''` for `g''_!` and the cover acyclicity `hcov` of the
amelioration. -/
@[stacks 08PK "L_n g_!(F') is the sheaf of H_n(I_U, F'_U); assumes 07AC and cover acyclicity"]
def derivedAbelianLowerShriekHomologyObjIsoFiberHomologySheaf
    (h : S.AbelianLowerShriekAcyclic)
    (h'' : (amelioratedSituation S).AbelianLowerShriekAcyclic)
    (hcov : (amelioratedSituation S).UliftFreeCoverLowerShriekAcyclic) (n : ℕ)
    (F' : Sheaf S.sourceTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}) :
    (S.derivedAbelianLowerShriekHomology n).obj F' ≅
      fiberHomologySheaf (amelioratedSituation S)
        ((amelioratedLowerShriek S).obj F').obj n :=
  derivedAbelianLowerShriekHomologyAmelioratedObjIso S h h'' n F' ≪≫
    (amelioratedSituation S).derivedLowerShriekHomologyObjIso h'' hcov n _

end Derived

end MorphismSituation

end Stacks.Sites.FibredCategory

end
