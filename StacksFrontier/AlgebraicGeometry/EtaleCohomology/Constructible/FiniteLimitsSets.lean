module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyConstantExtensions
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLocallyConstantLimitCategory
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.IteratedRefinement
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.SmallEtaleInverseImageModuleExact
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.StratumPullback
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.WeakSerre.FiniteTypeLocallyConstant
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.AbelianWeakSerre
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.FiniteLimits
public import StacksCore.Tactic.StacksAttribute

/-!
# Finite limits and colimits of constructible étale sheaves of sets

Let `X` be a scheme. The constructible sheaves of sets on the small étale site of `X` are closed
under finite limits and under finite colimits inside the category of all sheaves of sets on that
site.

Tag 03RZ has three parts, and the third is also carried here: for `Λ` a Noetherian ring, the
constructible sheaves of `Λ`-modules on the small étale site of a scheme form a weak Serre
subcategory of all sheaves of `Λ`-modules on it. The proof is the module analogue of the abelian
one in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.WeakSerre.ConstructibleAbelian`, and
the three inputs it needs for module coefficients are now available: left exactness of inverse
image (`AlgebraicGeometry.preservesFiniteLimits_smallEtaleSheafPullback_moduleCat`), Tag 093U (3)
(`Stacks.ConstantSheaf.isWeakSerreClass_isFiniteTypeLocallyConstantModuleSheaf`), and the
simultaneous stratification of a finite family of sheaves
(`AlgebraicGeometry.exists_stratification_isStratifiedSheaf_forall`).

## Main results

* `AlgebraicGeometry.isConstructibleSetSheaf_limit` and
  `AlgebraicGeometry.isConstructibleSetSheaf_colimit` — Stacks 03RZ for sheaves of sets.
* `AlgebraicGeometry.SmallEtale.isWeakSerreClass_isConstructibleModuleSheaf` — Stacks 03RZ (3),
  the weak Serre property for constructible sheaves of modules over a Noetherian ring.

## Implementation notes

Both statements reduce to Stacks 093U (1), the same closure property for *finite locally
constant* sheaves of sets on a site, once a single constructible stratification is found on which
every object of the finite diagram is finite locally constant. That stratification is a common
refinement of the finitely many stratifications the objects of the diagram provide, taken by
`AlgebraicGeometry.ConstructibleStratification.refineFinite`, and refined further against the
one-stratum stratification so that it is a stratification of the affine open at issue even when
the diagram is empty.

Restriction to a stratum then has to commute with the limit: it preserves finite limits by Stacks
03Q1 and finite colimits because it is a left adjoint.

**The module coefficient universe is `ModuleCat.{max (u + 1) w} Λ` and cannot be lowered.** Tag
093U (3) is stated on a site with objects in `Type c` and morphisms in `Type v` for coefficients
in `ModuleCat.{max c v w} Λ`; the small étale site of Tag 021B has objects in `Type (u + 1)` and
morphisms in `Type u`, so its coefficient universe is `max (u + 1) w`. In particular the ring
universe is not absorbed, unlike in
`AlgebraicGeometry.SmallEtale.hasSheafify_moduleCat`, which is why the two side conditions of
`AlgebraicGeometry.IsConstructibleModuleSheaf` are rederived here at this universe rather than
taken from
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.CoefficientHypotheses`.

## References

* [Stacks Project, Tag 03RZ](https://stacks.math.columbia.edu/tag/03RZ)
* [Stacks Project, Tag 093U](https://stacks.math.columbia.edu/tag/093U)
* [Stacks Project, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)
* [Stacks Project, Tag 0754](https://stacks.math.columbia.edu/tag/0754)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.ConstantSheaf
open scoped ZeroObject

namespace AlgebraicGeometry

universe v u
universe w r

variable (B : BigEtaleSite.{u}) (X : B.Scheme)

/-- The direct image of sheaves of sets along the localization of small étale base change at an
object of the source site has a left adjoint. This is what lets local constancy be transported
along inverse image: the trivializing covering of a finite locally constant sheaf is compared
with its image after restricting to a slice. -/
public instance isRightAdjoint_sheafPushforwardContinuous_overPost_smallEtale
    {S T : B.Scheme} (f : T ⟶ S) (V : SmallEtale B S.obj S.property) :
    ((Over.post (X := V) (smallEtaleBaseChange B f)).sheafPushforwardContinuous (Type (u + 1))
      ((SmallEtale.topology B S.obj S.property).over V)
      ((SmallEtale.topology B T.obj T.property).over
        ((smallEtaleBaseChange B f).obj V))).IsRightAdjoint :=
  inferInstance

/-- Inverse image of sheaves of sets along small étale base change. -/
public abbrev smallEtaleSetPullback {S T : B.Scheme} (f : T ⟶ S) :
    Sheaf (SmallEtale.topology B S.obj S.property) (Type (u + 1)) ⥤
      Sheaf (SmallEtale.topology B T.obj T.property) (Type (u + 1)) :=
  smallEtaleSheafPullback B (Type (u + 1)) f

variable {I : Type v} [SmallCategory I] [FinCategory I]

/-- **One stratification for a finite family of constructible sheaves of sets.** A finite family
of constructible sheaves of sets on the small étale site of `X` becomes finite locally constant
on every stratum of a single constructible stratification of a given affine open. -/
public theorem exists_stratification_isFiniteLocallyConstant
    (F : I ⥤ Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1)))
    (hF : ∀ i, IsConstructibleSetSheaf B X (F.obj i)) (U : X.obj.affineOpens) :
    ∃ r : ConstructibleStratification B X U.1, ∀ (k : Fin r.n) (i : I),
      IsFiniteLocallyConstant
        (SmallEtale.topology B (r.piece k).obj (r.piece k).property)
        ((smallEtaleSetPullback B (r.inclusion k)).obj (F.obj i)) := by
  classical
  choose s hs using fun i => hF i U
  exact ⟨ConstructibleStratification.refineFinite s (ConstructibleStratification.single B X U.1),
    fun k i => ConstructibleStratification.isFiniteLocallyConstant_of_refines _ (F.obj i) (hs i)
      (ConstructibleStratification.refineFinite_refines s _ i) k⟩

/-- A sheaf of sets is constructible once its inverse image to every stratum of a stratification
on which the finite family `F` is finite locally constant is finite locally constant. -/
private theorem isConstructibleSetSheaf_of_isFiniteLocallyConstant_pullback
    (F : I ⥤ Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1)))
    (hF : ∀ i, IsConstructibleSetSheaf B X (F.obj i))
    (G : Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1)))
    (h : ∀ {T : B.Scheme} (f : T ⟶ X),
      (∀ i, IsFiniteLocallyConstant (SmallEtale.topology B T.obj T.property)
        ((smallEtaleSetPullback B f).obj (F.obj i))) →
      IsFiniteLocallyConstant (SmallEtale.topology B T.obj T.property)
        ((smallEtaleSetPullback B f).obj G)) :
    IsConstructibleSetSheaf B X G := fun U => by
  obtain ⟨r, hr⟩ := exists_stratification_isFiniteLocallyConstant B X F hF U
  exact ⟨r, fun k => h _ (hr k)⟩

/-- **Stacks 03RZ for sheaves of sets, finite limits.** A finite limit of constructible sheaves
of sets on the small étale site of a scheme is constructible. -/
@[stacks 03RZ "constructible_sets_finite_limits_colimits", sga "4 IX 2.6" "(i bis) finite limits"]
public theorem isConstructibleSetSheaf_limit
    (F : I ⥤ Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1)))
    (hF : ∀ i, IsConstructibleSetSheaf B X (F.obj i)) :
    IsConstructibleSetSheaf B X (limit F) := by
  refine isConstructibleSetSheaf_of_isFiniteLocallyConstant_pullback B X F hF _ fun f hf => ?_
  have : IsFiniteLocallyConstant (SmallEtale.topology B _ _)
      (limit (F ⋙ smallEtaleSetPullback B f)) :=
    isFiniteLocallyConstant_limit_of_finCategory.{u, u + 1, 0, v} _ _ hf
  exact isFiniteLocallyConstant_congr _ (preservesLimitIso (smallEtaleSetPullback B f) F).symm

/-- **Stacks 03RZ for sheaves of sets, finite colimits.** A finite colimit of constructible
sheaves of sets on the small étale site of a scheme is constructible. -/
@[stacks 03RZ "constructible_sets_finite_limits_colimits", sga "4 IX 2.6" "(i bis) finite colimits"]
public theorem isConstructibleSetSheaf_colimit
    (F : I ⥤ Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1)))
    (hF : ∀ i, IsConstructibleSetSheaf B X (F.obj i)) :
    IsConstructibleSetSheaf B X (colimit F) := by
  refine isConstructibleSetSheaf_of_isFiniteLocallyConstant_pullback B X F hF _ fun f hf => ?_
  have := ((smallEtaleBaseChange B f).sheafAdjunctionContinuous (Type (u + 1))
    (SmallEtale.topology B X.obj X.property)
    (SmallEtale.topology B _ _)).leftAdjoint_preservesColimits
  have : IsFiniteLocallyConstant (SmallEtale.topology B _ _)
      (colimit (F ⋙ smallEtaleSetPullback B f)) :=
    isFiniteLocallyConstant_colimit_of_finCategory.{u, u + 1, 0, v} _ _ hf
  exact isFiniteLocallyConstant_congr _ (preservesColimitIso (smallEtaleSetPullback B f) F).symm

/-! ### Constructible sheaves of modules over a Noetherian ring -/

section Modules

variable (Λ : Type r) [Ring Λ]

/-- Pushforward of sheaves of `Λ`-modules along small étale base change, with coefficients in
`ModuleCat.{max (u + 1) w} Λ`, is a right adjoint.

`AlgebraicGeometry.SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat` is the same
statement at `ModuleCat.{max (u + 1) r w} Λ`, where the ring universe is absorbed too; the
coefficient universe here is built from the site alone, which is where Tag 093U (3) is available
on this site. -/
public theorem SmallEtale.isRightAdjointPushforward_moduleCat {S T : B.Scheme} (f : T ⟶ S) :
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{max (u + 1) w} Λ)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint :=
  inferInstance

/-- Presheaves of `Λ`-modules on a localization of the small étale site admit weak
sheafification, with coefficients in `ModuleCat.{max (u + 1) w} Λ`.

This is what the definition of local constancy of finite type asks for, the local value of a
locally constant sheaf being a constant sheaf on a slice. -/
public theorem SmallEtale.hasWeakSheafifyOver_moduleCat (T : B.Scheme)
    (V : SmallEtale B T.obj T.property) :
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
      (ModuleCat.{max (u + 1) w} Λ) :=
  inferInstance

attribute [local instance] SmallEtale.isRightAdjointPushforward_moduleCat
  SmallEtale.hasWeakSheafifyOver_moduleCat
  preservesFiniteLimits_smallEtaleSheafPullback_moduleCat
  preservesFiniteColimits_smallEtaleSheafPullback_moduleCat
  additive_smallEtaleSheafPullback_moduleCat

variable [IsNoetherianRing Λ]

/-- **Stacks 03RZ (3).** For `Λ` a Noetherian ring, the constructible sheaves of `Λ`-modules on
the small étale site of a scheme form a weak Serre subcategory of all sheaves of `Λ`-modules on
that site. There is no hypothesis on the scheme.

The proof is the five term form of the weak Serre condition,
`CategoryTheory.ObjectProperty.isWeakSerreClass_iff_prop_obj₂_of_exact`. Given an exact
`ℱ₀ ⟶ ℱ₁ ⟶ ℱ₂ ⟶ ℱ₃ ⟶ ℱ₄` with the four outer terms constructible, fix an affine open and
stratify all four of them on one constructible stratification of it with
`AlgebraicGeometry.exists_stratification_isStratifiedSheaf_forall`. Inverse image to a stratum is
exact by `AlgebraicGeometry.preservesFiniteLimits_smallEtaleSheafPullback_moduleCat`, so the
restricted five term sequence is still exact, and on a stratum constructibility is local
constancy of finite type, which is a weak Serre condition by Tag 093U (3). Hence the restriction
of `ℱ₂` to each stratum is locally constant of finite type, which is constructibility of `ℱ₂`. -/
@[stacks 03RZ "constructible_modules_weak_serre", sga "4 IX 2.6"]
public theorem SmallEtale.isWeakSerreClass_isConstructibleModuleSheaf :
    ObjectProperty.IsWeakSerreClass
      (fun F : Sheaf (SmallEtale.topology B X.obj X.property)
        (ModuleCat.{max (u + 1) w} Λ) => IsConstructibleModuleSheaf B X Λ F) := by
  have hPIso : ∀ (T : B.Scheme) {F G : Sheaf (SmallEtale.topology B T.obj T.property)
      (ModuleCat.{max (u + 1) w} Λ)}, (F ≅ G) →
      isFiniteTypeLocallyConstantSmallEtaleSheaf.{max (u + 1) w, u, r} B Λ T F →
        isFiniteTypeLocallyConstantSmallEtaleSheaf.{max (u + 1) w, u, r} B Λ T G :=
    fun T _ _ e h => Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_congr
      (SmallEtale.topology B T.obj T.property) Λ e h
  have hPImm : ∀ (T T' : B.Scheme) (g : T' ⟶ T), IsImmersion (B.inclusion.map g) →
      ∀ G : Sheaf (SmallEtale.topology B T.obj T.property) (ModuleCat.{max (u + 1) w} Λ),
        isFiniteTypeLocallyConstantSmallEtaleSheaf.{max (u + 1) w, u, r} B Λ T G →
        isFiniteTypeLocallyConstantSmallEtaleSheaf.{max (u + 1) w, u, r} B Λ T'
          (((smallEtaleBaseChange B g).sheafPullback (ModuleCat.{max (u + 1) w} Λ)
            (SmallEtale.topology B T.obj T.property)
            (SmallEtale.topology B T'.obj T'.property)).obj G) :=
    fun _ _ g _ G h => isFiniteTypeLocallyConstant_smallEtaleSheafPullback B Λ g G h
  apply (ObjectProperty.isWeakSerreClass_iff_prop_obj₂_of_exact _).2
  refine ⟨⟨0, isConstructibleModuleSheaf_of_isFiniteTypeLocallyConstant B X Λ _
    (Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_zero.{u, u + 1, max (u + 1) w, r}
      (SmallEtale.topology B X.obj X.property) Λ)⟩, ?_⟩
  intro S hS h₀ h₁ h₃ h₄
  change IsConstructibleModuleSheaf B X Λ (S.obj' 2)
  intro V
  obtain ⟨s, hs⟩ := exists_stratification_isStratifiedSheaf_forall B X
    (isFiniteTypeLocallyConstantSmallEtaleSheaf.{max (u + 1) w, u, r} B Λ) hPIso hPImm
    (F := ![S.obj' 0, S.obj' 1, S.obj' 3, S.obj' 4])
    (fun j => by fin_cases j <;> assumption) V
  refine ⟨s, fun k => ?_⟩
  have : ObjectProperty.IsWeakSerreClass
      (isFiniteTypeLocallyConstantSmallEtaleSheaf.{max (u + 1) w, u, r} B Λ (s.piece k)) :=
    Stacks.ConstantSheaf.isWeakSerreClass_isFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, w}
      (SmallEtale.topology B (s.piece k).obj (s.piece k).property) Λ
  exact ObjectProperty.prop_obj₂_of_exact
    (P := isFiniteTypeLocallyConstantSmallEtaleSheaf.{max (u + 1) w, u, r} B Λ (s.piece k))
    ((((smallEtaleBaseChange B (s.inclusion k)).sheafPullback (ModuleCat.{max (u + 1) w} Λ)
      (SmallEtale.topology B X.obj X.property)
      (SmallEtale.topology B (s.piece k).obj
        (s.piece k).property)).mapComposableArrows 4).obj S)
    (Stacks.ConstantSheaf.mapComposableArrows_exact
      ((smallEtaleBaseChange B (s.inclusion k)).sheafPullback (ModuleCat.{max (u + 1) w} Λ)
        (SmallEtale.topology B X.obj X.property)
        (SmallEtale.topology B (s.piece k).obj (s.piece k).property)) S hS)
    (hs k 0) (hs k 1) (hs k 2) (hs k 3)

end Modules

end AlgebraicGeometry

end
