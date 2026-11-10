module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SmulAnnihilatesSubobject
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackPullbackStability
public import StacksFrontier.AlgebraicGeometry.Quot.QuotFunctorClosedImmersionPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModuleEssentialImage
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModuleEssentialImageExact
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionPointsInjective
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersions
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.IntegralFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperClosedSubsetImage
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportClosedFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.ZeroLocusClosedProperSupportUnconditional

/-!
# The direct image along a closed immersion is an isomorphism of Quot functors

Let `B` be an algebraic space, let `π : X ⟶ Y` be a closed immersion of algebraic spaces which
are separated and of finite presentation over `B`, and let `F` be a quasi-coherent `𝒪_X`-module.
Stacks 0DP4 asserts that the morphism `Quot_{F/X/B} ⟶ Quot_{π_*F/Y/B}` of Stacks 0DP1 is an
isomorphism.

Write `G = π_*F`.  Over a test scheme `T` of `B` the base change `π_T : X_T ⟶ Y_T` is a closed
immersion, and by Stacks 04CJ the direct image `π_{T,*}` is fully faithful with essential image
the `𝒪_{Y_T}`-modules annihilated by the ideal `𝓘` cutting out `X_T`.  The module `G_T` is
`π_{T,*}F_T`, so it is annihilated by `𝓘`; hence so is every submodule `K ⊆ G_T`, and `K` is a
direct image.  The cokernel of a morphism between direct images is a direct image, `π_{T,*}`
being exact and fully faithful, so `G_T/K` is a direct image `π_{T,*}Q`.  The four conditions of
Stacks 09TR descend from `π_{T,*}Q` to `Q`:

* `Q = π_T^*π_{T,*}Q` by Stacks 04CJ, part (2), so `Q` is quasi-coherent and of finite
  presentation because inverse images preserve both;
* flatness over `T` is read on stalks, where `Q` and `π_{T,*}Q` agree;
* the support of `π_{T,*}Q` is the image of the support of `Q`, and `π_T` is injective on
  points and proper, so the support of `Q` is the inverse image of that of `π_{T,*}Q`, which is
  proper over `T` by Stacks 0CZG.

This is the bijectivity of `Quot_{F/X/B}(T) ⟶ Quot_{G/Y/B}(T)` for every `T`.

The names below are in the namespace `AlgebraicGeometry`.

## Main definitions

* `Space.QuotPushforwardSituation.ofIsClosedImmersion`: the standing data of Stacks 0DP4, a
  closed immersion, read as standing data of Stacks 0DP1.

## Main results

* `Space.essImage_modulePushforward_cokernel_arrow`: a quotient of a direct image along a closed
  immersion is a direct image.
* `Space.isQuasicoherentOnSite_of_isQuasicoherentOnSite_modulePushforward`,
  `Space.isFinitePresentationOnSite_of_isFinitePresentationOnSite_modulePushforward` and
  `Space.hasProperSupport_of_hasProperSupport_modulePushforward`: quasi-coherence, finite
  presentation and proper support descend along the direct image by a closed immersion.
* `Space.QuotPushforwardSituation.isQuotModule_of_isQuotModule_modulePushforward`: a module whose
  direct image along `π_T` satisfies the four conditions of Stacks 09TR over `T` satisfies them
  itself.
* `Space.QuotPushforwardSituation.isIso_of_app_eq_kernelSubobject`: a morphism
  `Quot_{F/X/B} ⟶ Quot_{G/Y/B}` which over every test scheme sends a quotient to its direct
  image, read through an isomorphism `G_T ≅ π_{T,*}F_T`, is an isomorphism when `π` is a closed
  immersion.
* `Space.QuotPushforwardSituation.closedImmersionQuotInputs`: the two inputs of
  `Space.QuotPushforwardSituation.isIso_quotFunctorMap`, constructed.

## Implementation notes

The category of modules on the small étale site of an algebraic space is abelian by the
instances of `StacksFrontier/AlgebraicGeometry/Spaces/ModulesAbelian.lean`.  Two global instances
making every category of sheaves of modules abelian in a larger universe are imported along the
way; they leave universe constraints stuck when a lemma about an arbitrary abelian category is
applied to these modules, so they are switched off in this file.

## References

* [Stacks Project, Tag 0DP4](https://stacks.math.columbia.edu/tag/0DP4)
* [Stacks Project, Tag 0DP1](https://stacks.math.columbia.edu/tag/0DP1)
* [Stacks Project, Tag 04CJ](https://stacks.math.columbia.edu/tag/04CJ)
* [Stacks Project, Tag 09TR](https://stacks.math.columbia.edu/tag/09TR)
* [Stacks Project, Tag 0CZG](https://stacks.math.columbia.edu/tag/0CZG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

/- The global instances `Abelian (SheafOfModules.{max u v r w} O)` and its Grothendieck
counterpart leave a stuck universe constraint against the modules of the small étale site, whose
sections are pinned to the universe of the schemes; the abelian structure used here is the one of
`StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian`. -/
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace CategoryTheory.Functor

universe v₁ v₂ u₁ u₂

variable {D₁ : Type u₁} {D₂ : Type u₂} [Category.{v₁} D₁] [Category.{v₂} D₂] [Abelian D₁]
  [Abelian D₂] {L : D₁ ⥤ D₂}

/-- The isomorphism of constant functors on the one-point category given by `b : A ≅ L M`. -/
private def constIsoOfIso {A : D₂} {M : D₁} (b : A ≅ L.obj M) :
    (const (Discrete PUnit.{1})).obj A ≅ (const (Discrete PUnit.{1})).obj M ⋙ L :=
  NatIso.ofComponents (fun _ ↦ b) (by rintro ⟨⟨⟩⟩ ⟨⟨⟩⟩ ⟨⟨⟨⟩⟩⟩; simp)

/-- **Applying a fully faithful functor to quotients, read through an isomorphism, is
injective.**  For `b : A ≅ L M`, two quotients of `M` whose images under `L`, read in `A`
through `b`, have the same kernel agree.

This is `CategoryTheory.Functor.conjSubobject_injective` on the one-point category. -/
theorem kernelSubobject_comp_map_cokernel_π_injective [L.PreservesEpimorphisms]
    (hff : L.FullyFaithful) {A : D₂} {M : D₁} (b : A ≅ L.obj M) :
    Function.Injective fun K : Subobject M ↦ kernelSubobject (b.hom ≫ L.map (cokernel.π K.arrow)) :=
  conjSubobject_injective (constIsoOfIso b) hff ⟨⟨⟩⟩

/-- **A quotient of `A ≅ L M` whose quotient object is an image under a fully faithful `L` is
the image of a quotient of `M`.**

This is `CategoryTheory.Functor.exists_conjSubobject_eq` on the one-point category. -/
theorem exists_kernelSubobject_comp_map_cokernel_π_eq (hff : L.FullyFaithful) {A : D₂}
    {M : D₁} (b : A ≅ L.obj M) (K' : Subobject A)
    (hK' : L.essImage (cokernel K'.arrow)) :
    ∃ K : Subobject M, kernelSubobject (b.hom ≫ L.map (cokernel.π K.arrow)) = K' ∧
      Nonempty (L.obj (cokernel K.arrow) ≅ cokernel K'.arrow) :=
  exists_conjSubobject_eq (constIsoOfIso b) hff (M := ⟨⟨⟩⟩) K' hK'

end CategoryTheory.Functor

namespace AlgebraicGeometry.Space

universe u

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Being proper over the base is a property of the closed set of points and of the morphism
alone, so it transports along equalities of both. -/
theorem isProperOver_congr {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {hX : IsAlgebraicSpace B S hS X} {hY : IsAlgebraicSpace B S hS Y} {f f' : X ⟶ Y}
    (hff : f = f') {hf : IsLocallyOfFiniteType B S hS f} {hf' : IsLocallyOfFiniteType B S hS f'}
    {T T' : Set (points B S hS X)} (hTT : T = T') {hT : IsClosed T} {hT' : IsClosed T'}
    (h : IsProperOver B S hS hX hY f hf T hT) : IsProperOver B S hS hX hY f' hf' T' hT' := by
  subst hff hTT
  exact h

/-! ### Descent of module conditions along a closed immersion -/

section Descent

variable (B S hS)

/-- **A quotient of a direct image along a closed immersion is a direct image.**  If `M` is a
direct image along the closed immersion `i` and `K ⊆ M`, then `M/K` is a direct image.

`M` is annihilated by the ideal cutting out `Z`, hence so is its submodule `K`, which is
therefore a direct image by the essential-image assertion of Stacks 04CJ, part (3); and the
cokernel of a morphism between direct images is a direct image, `i_*` being exact and fully
faithful. -/
theorem essImage_modulePushforward_cokernel_arrow {Z X : AlgebraicSpaces B S hS} (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) {M : Modules.{u, u} B S hS X.1 X.2}
    (hM : (modulePushforward B S hS i).essImage M) (K : Subobject M) :
    (modulePushforward B S hS i).essImage (cokernel K.arrow) := by
  have hK : (modulePushforward B S hS i).essImage (K : Modules.{u, u} B S hS X.1 X.2) :=
    essImage_modulePushforward_of_annihilatedByKerIdeal B S hS i hi _ fun U a ha m =>
      Stacks.SheafOfModules.smul_eq_zero_of_mono K.arrow U a
        (annihilatedByKerIdeal_of_essImage_modulePushforward B S hS i hM U a ha) m
  exact essImage_modulePushforward_cokernel B S hS i hi hK hM K.arrow

/-- **Quasi-coherence descends along the direct image by a closed immersion.**  If `i_*H` is
quasi-coherent then so is `H`, which is `i^*i_*H` by Stacks 04CJ, part (2), an inverse image of
a quasi-coherent module. -/
theorem isQuasicoherentOnSite_of_isQuasicoherentOnSite_modulePushforward
    {Z X : AlgebraicSpaces B S hS} (i : Z ⟶ X) (hi : IsClosedImmersion B S hS i.hom)
    (H : Modules.{u, u} B S hS Z.1 Z.2)
    (h : ((modulePushforward B S hS i).obj H).IsQuasicoherentOnSite) :
    H.IsQuasicoherentOnSite :=
  SheafOfModules.IsQuasicoherentOnSite.of_iso ((modulePullbackCounitIso B S hS i hi).app H)
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS i _ h)

/-- **Finite presentation descends along the direct image by a closed immersion.**  If `i_*H` is
of finite presentation then so is `H`, which is `i^*i_*H` by Stacks 04CJ, part (2). -/
theorem isFinitePresentationOnSite_of_isFinitePresentationOnSite_modulePushforward
    {Z X : AlgebraicSpaces B S hS} (i : Z ⟶ X) (hi : IsClosedImmersion B S hS i.hom)
    (H : Modules.{u, u} B S hS Z.1 Z.2)
    (h : ((modulePushforward B S hS i).obj H).IsFinitePresentationOnSite) :
    H.IsFinitePresentationOnSite :=
  SheafOfModules.IsFinitePresentationOnSite.of_iso ((modulePullbackCounitIso B S hS i hi).app H)
    (isFinitePresentationOnSite_modulePullback B S hS i _ h)

/-- **Proper support descends along the direct image by a closed immersion.**  Let
`i : Z ⟶ X` be a closed immersion, `g : X ⟶ Y` locally of finite type and `H` an
`𝒪_Z`-module of finite type.  If `i_*H` has support proper over `Y` along `g`, then `H` has
support proper over `Y` along `g' = i ≫ g`.

The support of `H` is closed by Stacks 07TZ; the support of `i_*H` is its image, and `i` is
injective on points, so the support of `H` is the inverse image of that of `i_*H`, which is
proper over `Y` because `i` is proper (Stacks 04XZ, Stacks 0CZG). -/
theorem hasProperSupport_of_hasProperSupport_modulePushforward
    {Z X : AlgebraicSpaces B S hS} {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) (i : Z ⟶ X) (hi : IsClosedImmersion B S hS i.hom)
    (g : X.1 ⟶ Y) (hg : IsLocallyOfFiniteType B S hS g) {g' : Z.1 ⟶ Y}
    (hg' : IsLocallyOfFiniteType B S hS g') (hcomp : i.hom ≫ g = g')
    (H : Modules.{u, u} B S hS Z.1 Z.2) [hH : SheafOfModules.IsFiniteTypeOnSite H]
    (h : HasProperSupport B S hS X.2 hY g hg
      ((SheafOfModules.toSheaf _).obj ((modulePushforward B S hS i).obj H))) :
    HasProperSupport B S hS Z.2 hY g' hg' ((SheafOfModules.toSheaf _).obj H) := by
  subst hcomp
  have hcl := isClosed_supportOfSheaf_of_isFiniteTypeOnSite B S hS Z.1 Z.2 H
  have heq := supportOfSheaf_modulePushforward_eq_image_of_isClosedImmersion B S hS i hi H hcl
  have hinj := pointsMap_hom_injective_of_isClosedImmersion B S hS i hi
  obtain ⟨hTcl, hTproper⟩ := h
  have key := isProperOver_preimage_of_isProper B S hS Z.2 X.2 hY i.hom g
    (isProper_of_isClosedImmersion B S hS Z.2 X.2 i.hom hi) hg' hg _ hTcl hTproper
  refine ⟨hcl, isProperOver_congr rfl ?_ key⟩
  rw [heq]
  exact Set.preimage_image_eq _ hinj

end Descent

namespace QuotPushforwardSituation

/-! ### The standing data of Stacks 0DP4 -/

/-- **The standing data of Stacks 0DP4**: a closed immersion `π : X ⟶ Y` of algebraic spaces
which are separated and of finite presentation over an algebraic space `B`, together with a
quasi-coherent `𝒪_X`-module `F`.  A closed immersion is affine (Stacks 07U2) and finite
(Stacks 081Y), hence quasi-finite (Stacks 04NY), so this is the standing data of Stacks 0DP1. -/
def ofIsClosedImmersion (base X Y : AlgebraicSpaces B S hS) (π : X ⟶ Y)
    (hπ : IsClosedImmersion B S hS π.hom) (structureX : X ⟶ base) (structureY : Y ⟶ base)
    (comp : π ≫ structureY = structureX) (F : Modules.{u, u} B S hS X.1 X.2)
    (quasicoherent : F.IsQuasicoherentOnSite) (separatedX : IsSeparated B S hS structureX.hom)
    (separatedY : IsSeparated B S hS structureY.hom)
    (finitePresentationX : IsFinitePresentation B S hS structureX.hom)
    (finitePresentationY : IsFinitePresentation B S hS structureY.hom) :
    QuotPushforwardSituation B S hS where
  base := base
  X := X
  Y := Y
  π := π
  structureX := structureX
  structureY := structureY
  comp := comp
  F := F
  quasicoherent := quasicoherent
  affine := isAffineHom_of_isClosedImmersion B S hS π.hom hπ
  quasiFinite := isQuasiFinite_of_isFinite B S hS π.hom X.2 Y.2
    (isFinite_of_isClosedImmersion B S hS π.hom hπ)
  separatedX := separatedX
  separatedY := separatedY
  finitePresentationX := finitePresentationX
  finitePresentationY := finitePresentationY

variable (D : QuotPushforwardSituation B S hS)

/-! ### Every quotient of `G_T` is a direct image -/

/-- **Every quotient of `G_T` is a direct image along `π_T`**, for a closed immersion `π`.

`G_T` is the direct image `π_{T,*}F_T` through the comparison of Stacks 07U8, so it is
annihilated by the ideal cutting out `X_T`; a submodule of an annihilated module is annihilated,
hence a direct image by the essential-image assertion of Stacks 04CJ, part (3); and the cokernel
of a morphism between direct images is a direct image. -/
theorem essImage_quotientModule_of_isClosedImmersion
    (h : SchemeTargetAffinePushforwardQuasicoherent B S hS) (c : PushforwardComparison D)
    (hπ : IsClosedImmersion B S hS D.π.hom) (T : SchemesOver D.base)
    (K : Subobject ((D.targetSituation h).baseChangeModule T)) :
    (modulePushforward B S hS (D.baseChangeOfMap T)).essImage
      ((D.targetSituation h).quotientModule T K) :=
  essImage_modulePushforward_cokernel_arrow B S hS _ (D.isClosedImmersion_baseChangeOfMap hπ T)
    ⟨_, ⟨((c.iso T).app D.F).symm⟩⟩ K

/-! ### The four conditions of Stacks 09TR descend along `π_{T,*}` -/

/-- **The four conditions of Stacks 09TR descend along the direct image by a closed
immersion.**  If the direct image `π_{T,*}Q` of an `𝒪_{X_T}`-module `Q` is quasi-coherent, flat
over `T`, of finite presentation and has support proper over `T`, then so has `Q`. -/
theorem isQuotModule_of_isQuotModule_modulePushforward
    (h : SchemeTargetAffinePushforwardQuasicoherent B S hS)
    (hπ : IsClosedImmersion B S hS D.π.hom) (T : SchemesOver D.base)
    (Q : Modules.{u, u} B S hS (D.sourceSituation.space T).1 (D.sourceSituation.space T).2)
    (hQ : (D.targetSituation h).IsQuotModule T
      ((modulePushforward B S hS (D.baseChangeOfMap T)).obj Q)) :
    D.sourceSituation.IsQuotModule T Q := by
  obtain ⟨hqc, hflat, hfp, hprop⟩ := hQ
  have hi := D.isClosedImmersion_baseChangeOfMap hπ T
  have hcomp : D.baseChangeOfMap T ≫ (D.targetSituation h).projection T =
      D.sourceSituation.projection T :=
    D.baseChangeOfMap_comp_inclusion T
  have hQqc : Q.IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_of_isQuasicoherentOnSite_modulePushforward B S hS _ hi Q hqc
  have hQfp : Q.IsFinitePresentationOnSite :=
    isFinitePresentationOnSite_of_isFinitePresentationOnSite_modulePushforward B S hS _ hi Q hfp
  refine ⟨hQqc, ?_, hQfp, ?_⟩
  · exact hcomp ▸ @isFlatOver_of_isFlatOver_modulePushforward B S hS _ _ _ (D.baseChangeOfMap T)
      hi ((D.targetSituation h).projection T) Q hQqc hqc hflat
  · exact hasProperSupport_of_hasProperSupport_modulePushforward B S hS
      ((schemeSpaceFunctor B S hS).obj T.left).2 (D.baseChangeOfMap T) hi
      ((D.targetSituation h).projection T).hom
      ((D.targetSituation h).isLocallyOfFiniteType_projection T)
      (D.sourceSituation.isLocallyOfFiniteType_projection T) (congrArg (·.hom) hcomp) Q
      (hH := @SheafOfModules.isFiniteTypeOnSite_of_isFinitePresentationOnSite _ _ _ _ Q hQfp)
      hprop

/-! ### The direct image of quotients is a bijection -/

/-- **The direct image of quotients along a closed immersion is injective.**  For any
isomorphism `b : G_T ≅ π_{T,*}F_T`, two quotients of `F_T` whose direct images, read in `G_T`
through `b`, have the same kernel agree, `π_{T,*}` being fully faithful (Stacks 04CJ). -/
theorem kernelSubobject_comp_map_quotientProjection_injective
    (h : SchemeTargetAffinePushforwardQuasicoherent B S hS)
    (hπ : IsClosedImmersion B S hS D.π.hom) (T : SchemesOver D.base)
    (b : (D.targetSituation h).baseChangeModule T ≅
      (modulePushforward B S hS (D.baseChangeOfMap T)).obj (D.sourceSituation.baseChangeModule T)) :
    Function.Injective fun K ↦ kernelSubobject
      (b.hom ≫ (modulePushforward B S hS (D.baseChangeOfMap T)).map
        (D.sourceSituation.quotientProjection T K)) :=
  have := preservesEpimorphisms_modulePushforward_of_isClosedImmersion B S hS _
    (D.isClosedImmersion_baseChangeOfMap hπ T)
  Functor.kernelSubobject_comp_map_cokernel_π_injective
    (D.fullyFaithfulPushforwardBaseChangeOfMap hπ T) b

/-- **Every member of `Quot_{G/Y/B}(T)` is the direct image of a member of `Quot_{F/X/B}(T)`**,
for a closed immersion and any isomorphism `b : G_T ≅ π_{T,*}F_T` through which direct images
of quotients are read.

The quotient of `G_T` is a direct image `π_{T,*}Q` by
`AlgebraicGeometry.Space.essImage_modulePushforward_cokernel_arrow`, hence the direct image of a
quotient `Q` of `F_T`, `π_{T,*}` being fully faithful; and the four conditions of Stacks 09TR
descend from `π_{T,*}Q` to `Q`. -/
theorem exists_kernelSubobject_comp_map_quotientProjection_eq
    (h : SchemeTargetAffinePushforwardQuasicoherent B S hS)
    (hπ : IsClosedImmersion B S hS D.π.hom) (T : SchemesOver D.base)
    (b : (D.targetSituation h).baseChangeModule T ≅
      (modulePushforward B S hS (D.baseChangeOfMap T)).obj (D.sourceSituation.baseChangeModule T))
    (K' : Subobject ((D.targetSituation h).baseChangeModule T))
    (hK' : K' ∈ (D.targetSituation h).properlySupportedQuotients T) :
    ∃ K ∈ D.sourceSituation.properlySupportedQuotients T, kernelSubobject
      (b.hom ≫ (modulePushforward B S hS (D.baseChangeOfMap T)).map
        (D.sourceSituation.quotientProjection T K)) = K' := by
  obtain ⟨K, hK, ⟨ι⟩⟩ := Functor.exists_kernelSubobject_comp_map_cokernel_π_eq
    (D.fullyFaithfulPushforwardBaseChangeOfMap hπ T) b K'
    (essImage_modulePushforward_cokernel_arrow B S hS _
      (D.isClosedImmersion_baseChangeOfMap hπ T) ⟨_, ⟨b.symm⟩⟩ K')
  exact ⟨K, (D.sourceSituation.mem_properlySupportedQuotients_iff T K).mpr
    (D.isQuotModule_of_isQuotModule_modulePushforward h hπ T _
      (QuotSituation.IsQuotModule.of_iso ι.symm
        (((D.targetSituation h).mem_properlySupportedQuotients_iff T K').mp hK'))), hK⟩

/-- **A morphism of Quot functors given by direct images of quotients along a closed immersion
is an isomorphism.**  Let `φ : Quot_{F/X/B} ⟶ Quot_{G/Y/B}` send, over every test scheme `T`, a
quotient of `F_T` with kernel `K` to the kernel of the projection `G_T ≅ π_{T,*}F_T ⟶
π_{T,*}(F_T/K)`, for some family of isomorphisms `b_T : G_T ⟶ π_{T,*}F_T`.  If `π` is a closed
immersion then `φ` is an isomorphism: over every test scheme it is a bijection. -/
theorem isIso_of_app_eq_kernelSubobject (h : SchemeTargetAffinePushforwardQuasicoherent B S hS)
    (hπ : IsClosedImmersion B S hS D.π.hom)
    (φ : D.sourceSituation.quotFunctor ⟶ (D.targetSituation h).quotFunctor)
    (b : ∀ T : SchemesOver D.base, (D.targetSituation h).baseChangeModule T ⟶
      (modulePushforward B S hS (D.baseChangeOfMap T)).obj (D.sourceSituation.baseChangeModule T))
    (hb : ∀ T, IsIso (b T))
    (hφ : ∀ (T : SchemesOver D.base) (K : D.sourceSituation.properlySupportedQuotients T),
      (φ.app (Opposite.op T) K).1 = kernelSubobject (b T ≫
        (modulePushforward B S hS (D.baseChangeOfMap T)).map
          (D.sourceSituation.quotientProjection T K.1))) :
    IsIso φ := by
  have happ : ∀ T, IsIso (φ.app T) := by
    rintro ⟨T⟩
    have := hb T
    rw [isIso_iff_bijective]
    refine ⟨fun x y hxy ↦ Subtype.ext ?_, fun y ↦ ?_⟩
    · exact D.kernelSubobject_comp_map_quotientProjection_injective h hπ T
        (asIso (b T))
        ((hφ T x).symm.trans ((congrArg Subtype.val hxy).trans (hφ T y)))
    · obtain ⟨K, hK, hconj⟩ := D.exists_kernelSubobject_comp_map_quotientProjection_eq h hπ
        T (asIso (b T)) y.1 y.2
      exact ⟨⟨K, hK⟩, Subtype.ext ((hφ T ⟨K, hK⟩).trans hconj)⟩
  exact NatIso.isIso_of_isIso_app _

/-! ### The inputs of the bijectivity, constructed -/

/-- **The two inputs of `AlgebraicGeometry.Space.QuotPushforwardSituation.isIso_quotFunctorMap`,
constructed** for a closed immersion: every quotient of `G_T` is a direct image along `π_T`, and
the four conditions of Stacks 09TR descend along `π_{T,*}`. -/
theorem closedImmersionQuotInputs (h : SchemeTargetAffinePushforwardQuasicoherent B S hS)
    (c : PushforwardComparison D) (hπ : IsClosedImmersion B S hS D.π.hom) :
    D.ClosedImmersionQuotInputs h where
  essImage_quotientModule T K := D.essImage_quotientModule_of_isClosedImmersion h c hπ T K
  isQuotModule_of_pushforward T Q := D.isQuotModule_of_isQuotModule_modulePushforward h hπ T Q

/-- **The morphism of Quot functors induced by the direct image along a closed immersion is an
isomorphism**, for every choice of the inputs of Stacks 0DP1 it is built from. -/
theorem isIso_quotFunctorMap_of_isClosedImmersion
    (h : SchemeTargetAffinePushforwardQuasicoherent B S hS)
    (I : D.AffinePushforwardQuotInputs h) (hπ : IsClosedImmersion B S hS D.π.hom) :
    IsIso (D.quotFunctorMap h I) :=
  D.isIso_quotFunctorMap h I (D.closedImmersionQuotInputs h I.comparison hπ) hπ

end QuotPushforwardSituation

end AlgebraicGeometry.Space

end
