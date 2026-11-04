module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Duality.CompactlySupportedCohomology.BaseChangeShriekLifting
public import StacksFrontier.AlgebraicGeometry.Duality.CompactlySupportedCohomology.ProperPushforwardDeligne
public import StacksFrontier.AlgebraicGeometry.Duality.CompactlySupportedCohomology.ShriekTrianglesData
public import StacksFrontier.AlgebraicGeometry.Duality.Compactification.PreservesInterior
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CompositionAssociativity

/-!
# Extension by zero and compactifications

Let `j : U ⟶ X` be an open immersion of Noetherian schemes and let `j' : U ⟶ X'` be a
compactification of `U` over `X`: an open immersion with `f : X' ⟶ X` proper and `j' ≫ f = j`.
[Stacks, Tag 0G4X] gives a canonical isomorphism

`Rj_! ≅ Rf_* ∘ R(j')_!`

of functors `D^b_{Coh}(𝒪_U) ⥤ Pro-D^b_{Coh}(𝒪_X)`. As a consequence the functor
`Rf_! = Rf̄_* ∘ Rj_!` of a morphism of `FTS_S` ([Stacks, Section 0G4Z]) does not depend on the
compactification, [Stacks, Tag 0G50].

## Main definitions

* `AlgebraicGeometry.derivedPushforwardModulesIdIso`: `R(𝟙)_* ≅ 𝟭`.
* `AlgebraicGeometry.derivedPushforwardModulesCompIso`: `Rf_* ∘ Rg_* ≅ R(f ≫ g)_*`, by
  [Stacks, Tag 0D5T].
* `AlgebraicGeometry.derivedPushforwardBaseChangeIso`: flat base change along open immersions,
  [Stacks, Tag 08FE], for a cartesian square of schemes.
* `AlgebraicGeometry.properPushforwardBoundedCoherentCompIso`: the composition isomorphism on
  `D^b_{Coh}`.
* `AlgebraicGeometry.compactificationShriekOfPreimage`: [Stacks, Tag 0G4X] when
  `j'(U) = f⁻¹(j(U))`, which is [Stacks, Tag 0G4W] read for `U` itself.
* `AlgebraicGeometry.CompactificationOf.closure`: the scheme-theoretic closure of `U` in a
  compactification.
* `AlgebraicGeometry.extensionByZeroCompactificationIso`: **[Stacks, Tag 0G4X]**.
* `AlgebraicGeometry.lowerShriekIso`: **[Stacks, Tag 0G50]**.

## References

* [Stacks Project, Tag 0G4X](https://stacks.math.columbia.edu/tag/0G4X)
* [Stacks Project, Tag 0G50](https://stacks.math.columbia.edu/tag/0G50)
* [Stacks Project, Tag 0ATU](https://stacks.math.columbia.edu/tag/0ATU)
* [Stacks Project, Tag 0G4W](https://stacks.math.columbia.edu/tag/0G4W)
* [Stacks Project, Tag 0D5T](https://stacks.math.columbia.edu/tag/0D5T)
* [Stacks Project, Tag 08FE](https://stacks.math.columbia.edu/tag/08FE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.pullback_preservesFiniteLimits_of_isOpenImmersion

universe u

namespace AlgebraicGeometry

/-! ### The derived direct image: identity, composition, base change -/

open Stacks.Cohomology.DerivedPushforwardAssociativity in
/-- **The derived direct image along the identity is the identity**: `R(𝟙 X)_* ≅ 𝟭`. Degreewise
pushforward along `𝟙 X` is the identity, so the identity of `D(𝒪_X)` is a right derived functor of
it. -/
public def derivedPushforwardModulesIdIso (X : Scheme.{u}) :
    derivedPushforwardModules (𝟙 X) ≅ 𝟭 (DerivedCategory X.Modules) :=
  let e : DerivedCategory.Qh ⋙ 𝟭 (DerivedCategory X.Modules) ≅
      (Scheme.Modules.pushforward (𝟙 X)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh :=
    DerivedCategory.Qh.rightUnitor ≪≫
      (Functor.isoWhiskerRight (natIsoMapHomotopyCategory (Scheme.Modules.pushforwardId X)
        (ComplexShape.up ℤ) ≪≫ mapHomotopyCategoryIdIso _ _) DerivedCategory.Qh ≪≫
        DerivedCategory.Qh.leftUnitor).symm
  haveI := Functor.isRightDerivedFunctor_of_inverts
    (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)) (𝟭 (DerivedCategory X.Modules)) e
  (Functor.rightDerivedNatIso (𝟭 (DerivedCategory X.Modules)) (derivedPushforwardModules (𝟙 X))
    e.inv (derivedPushforwardModulesUnit (𝟙 X))
    (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)) (Iso.refl _)).symm

open Stacks.Cohomology.DerivedPushforwardComposition in
/-- **The composition isomorphism for the derived direct image**, [Stacks, Tag 0D5T]:
`Rf_* ∘ Rg_* ≅ R(f ≫ g)_*` for quasi-compact quasi-separated `f` and `g`. -/
public def derivedPushforwardModulesCompIso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g] [QuasiSeparated g] :
    derivedPushforwardModules f ⋙ derivedPushforwardModules g ≅
      derivedPushforwardModules (f ≫ g) :=
  haveI := @isIso_derivedPushforwardComparison_unconditional _ _ _ _ _ _
    f.toLRSHom.toShHom g.toLRSHom.toShHom
    (derivedPushforwardModules f) (derivedPushforwardModules g) (derivedPushforwardModules (f ≫ g))
    (derivedPushforwardModulesUnit f) (derivedPushforwardModulesUnit g)
    (derivedPushforwardModulesUnit (f ≫ g)) (derivedPushforwardModules_isRightDerivedFunctor f)
    (derivedPushforwardModules_isRightDerivedFunctor g)
    (derivedPushforwardModules_isRightDerivedFunctor (f ≫ g))
  (asIso (@derivedPushforwardComparison _ _ _ _ _ _ f.toLRSHom.toShHom g.toLRSHom.toShHom
    (derivedPushforwardModules f) (derivedPushforwardModules g) (derivedPushforwardModules (f ≫ g))
    (derivedPushforwardModulesUnit f) (derivedPushforwardModulesUnit g)
    (derivedPushforwardModulesUnit (f ≫ g))
    (derivedPushforwardModules_isRightDerivedFunctor (f ≫ g)))).symm

/-- **Flat base change along open immersions**, [Stacks, Tag 08FE], for a cartesian square of
schemes
```
U --g--> V
|        |
i        j
v        v
X --f--> Y
```
in which `i` and `j` are open immersions: `(Rf_* K)|_V ≅ Rg_*(K|_U)`. -/
public def derivedPushforwardBaseChangeIso {U X V Y : Scheme.{u}} (f : X ⟶ Y) (i : U ⟶ X)
    (j : V ⟶ Y) (g : U ⟶ V) [IsOpenImmersion i] [IsOpenImmersion j] [QuasiCompact f]
    [QuasiSeparated f] [QuasiCompact g] [QuasiSeparated g] (hsq : IsPullback i g f j) :
    derivedPushforwardModules f ⋙ (Scheme.Modules.restrictFunctor j).mapDerivedCategory ≅
      (Scheme.Modules.restrictFunctor i).mapDerivedCategory ⋙ derivedPushforwardModules g := by
  let Fi := Scheme.Modules.pullback i
  let Fj := Scheme.Modules.pullback j
  let Ri := Fi.mapDerivedCategory
  let Rj := Fj.mapDerivedCategory
  have hiR : Ri.IsRightDerivedFunctor Fi.mapDerivedCategoryFactorsh.inv
      (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)) :=
    Functor.isRightDerivedFunctor_of_inverts _ Ri Fi.mapDerivedCategoryFactorsh
  have hjR : Rj.IsRightDerivedFunctor Fj.mapDerivedCategoryFactorsh.inv
      (HomotopyCategory.quasiIso Y.Modules (ComplexShape.up ℤ)) :=
    Functor.isRightDerivedFunctor_of_inverts _ Rj Fj.mapDerivedCategoryFactorsh
  let e : derivedPushforwardModules f ⋙ Rj ≅ Ri ⋙ derivedPushforwardModules g :=
    @Stacks.Cohomology.derivedPushforwardRestrictIso _ _ _ _
      f.toLRSHom.toShHom i.toLRSHom.toShHom j.toLRSHom.toShHom g.toLRSHom.toShHom _ _
      (isPullback_toShHom i g f j hsq) _ _ _ _
      (derivedPushforwardModules f) (derivedPushforwardModules g) Ri Rj
      (derivedPushforwardModulesUnit f) (derivedPushforwardModulesUnit g)
      Fi.mapDerivedCategoryFactorsh.inv Fj.mapDerivedCategoryFactorsh.inv
      (derivedPushforwardModules_isRightDerivedFunctor f)
      (derivedPushforwardModules_isRightDerivedFunctor g) hiR hjR
  exact Functor.isoWhiskerLeft _
      (Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _
        (Scheme.Modules.restrictFunctorIsoPullback j)) ≪≫ e ≪≫
    Functor.isoWhiskerRight
      (Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _
        (Scheme.Modules.restrictFunctorIsoPullback i)).symm _

/-! ### On bounded coherent derived categories -/

/-- **The composition isomorphism on `D^b_{Coh}`**: for proper morphisms `f : X ⟶ Y`,
`g : Y ⟶ Z` of Noetherian schemes, `Rg_* ∘ Rf_* ≅ R(f ≫ g)_*` on bounded coherent derived
categories, [Stacks, Tag 0D5T]. -/
public def properPushforwardBoundedCoherentCompIso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsNoetherian Y] [IsNoetherian Z] [IsProper f] [IsProper g] :
    properPushforwardBoundedCoherent f ⋙ properPushforwardBoundedCoherent g ≅
      properPushforwardBoundedCoherent (f ≫ g) :=
  NatIso.ofComponents
    (fun K => (boundedCoherentDerived Z).fullyFaithfulι.preimageIso
      ((derivedPushforwardModulesCompIso f g).app K.obj))
    (fun {K L} φ => (boundedCoherentDerived Z).ι.map_injective (by
      simpa using (derivedPushforwardModulesCompIso f g).hom.naturality
        ((boundedCoherentDerived X).ι.map φ)))

/-- **Restriction to an open of the target whose preimage is an open of the source isomorphic to
it.** For `j' : U ⟶ X'` and `j : U ⟶ X` open immersions and `f : X' ⟶ X` with `j' ≫ f = j` and
`f⁻¹(j(U)) = j'(U)`, `(Rf_* K)|_U ≅ K|_U` on `D^b_{Coh}`. -/
public def properPushforwardRestrictIsoOfPreimage {U X' X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (j' : U ⟶ X') [IsOpenImmersion j'] (f : X' ⟶ X) [IsNoetherian X]
    [IsNoetherian X'] [IsProper f] (hf : j' ≫ f = j) (hU : f ⁻¹ᵁ j.opensRange = j'.opensRange) :
    properPushforwardBoundedCoherent f ⋙ restrictBoundedCoherentLift j ≅
      restrictBoundedCoherentLift j' ⋙ 𝟭 (BoundedCoherentDerived U) :=
  have hsq : IsPullback j' (𝟙 U) f j :=
    (IsOpenImmersion.isPullback (𝟙 U) j' j f (by rw [hf, Category.id_comp]) hU).flip
  let e : derivedPushforwardModules f ⋙ (Scheme.Modules.restrictFunctor j).mapDerivedCategory ≅
      (Scheme.Modules.restrictFunctor j').mapDerivedCategory :=
    derivedPushforwardBaseChangeIso f j' j (𝟙 U) hsq ≪≫
      Functor.isoWhiskerLeft _ (derivedPushforwardModulesIdIso U) ≪≫ Functor.rightUnitor _
  NatIso.ofComponents
    (fun K => (boundedCoherentDerived U).fullyFaithfulι.preimageIso (e.app K.obj))
    (fun {K L} φ => (boundedCoherentDerived U).ι.map_injective (by
      simpa using e.hom.naturality ((boundedCoherentDerived X').ι.map φ)))

/-! ### Extension by zero and compactifications -/

/-- **[Stacks, Tag 0G4X] when `j'(U) = f⁻¹(j(U))`.** Let `j : U ⟶ X` and `j' : U ⟶ X'` be open
immersions into Noetherian schemes and `f : X' ⟶ X` proper with `j' ≫ f = j` and
`f⁻¹(j(U)) = j'(U)`. Then `Rj_! ≅ Rf_* ∘ R(j')_!`.

This is the first proof of [Stacks, Tag 0G4W] read for `U` itself: for a Deligne system `(K_n)`
along `j'` with value `K`, the system `(Rf_* K_n)` is pro-isomorphic to a Deligne system along `j`
(`AlgebraicGeometry.proIsoDeligneSystem_properPushforward` for the open `j(U)`, whose preimage is
`j'(U)`), and it restricts on `U` to the constant system at `K`
(`AlgebraicGeometry.properPushforwardRestrictIsoOfPreimage`), so it represents `Rj_! K`;
`CategoryTheory.baseChangeShriekOfLifting` makes this natural in `K`. -/
public def compactificationShriekOfPreimage {U X' X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (j' : U ⟶ X') [IsOpenImmersion j'] (f : X' ⟶ X) [IsNoetherian X]
    [IsNoetherian X'] [IsProper f] (hf : j' ≫ f = j) (hU : f ⁻¹ᵁ j.opensRange = j'.opensRange) :
    extensionByZeroOpenImmersion j ≅
      extensionByZeroOpenImmersion j' ⋙ ProSeq.map (properPushforwardBoundedCoherent f) :=
  (Functor.leftUnitor _).symm ≪≫
    baseChangeShriekOfLifting (DeligneSystem.values j') (DeligneSystem.values j)
      (properPushforwardBoundedCoherent f) (𝟭 _)
      (properPushforwardRestrictIsoOfPreimage j j' f hf hU) fun K N => by
        have hV : Set.range j.base = Set.range j.opensRange.ι.base := by
          rw [Scheme.Opens.range_ι]
          rfl
        have hW : Set.range j'.base = Set.range (f ⁻¹ᵁ j.opensRange).ι.base := by
          rw [Scheme.Opens.range_ι, hU]
          rfl
        let D := (DeligneSystem.ofValue j' K).congrRange hW
        have h : ProIsoDeligneSystem j
            ((DeligneSystem.values j').system K ⋙ properPushforwardBoundedCoherent f) :=
          (ProIsoDeligneSystem.congr_range hV).mpr
            (proIsoDeligneSystem_comp_of_iso (properPushforwardBoundedCoherent f)
              D.proObjectIsoValues
              (proIsoDeligneSystem_properPushforward f j.opensRange D.value))
        exact (DeligneSystem.values j).restrictionLifting_of_proIsoDeligne
          (proIsoDeligneSystem_iff.mp h) N

/-- `Rf_*` on `D^b_{Coh}` along equal morphisms. -/
public def properPushforwardBoundedCoherentCongr {X Y : Scheme.{u}} [IsNoetherian Y] {f g : X ⟶ Y}
    [IsProper f] [IsProper g] (h : f = g) :
    properPushforwardBoundedCoherent f ≅ properPushforwardBoundedCoherent g := by
  subst h
  exact Iso.refl _

section Closure

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [IsNoetherian X]
  (c : CompactificationOf (Over.mk j))

/-- The open immersion of a compactification of an open of a Noetherian scheme is quasi-compact,
its source being a Noetherian space. -/
public instance CompactificationOf.quasiCompact_immersion_of_isNoetherian :
    QuasiCompact c.immersion :=
  have : TopologicalSpace.NoetherianSpace U := j.isOpenEmbedding.isInducing.noetherianSpace
  inferInstance

omit [IsOpenImmersion j] [IsNoetherian X] in
/-- The open immersion of `U` into the scheme-theoretic closure, followed by the proper map to `X`,
is `j`. -/
public lemma CompactificationOf.toImage_imageι_toBase :
    c.immersion.toImage ≫ c.immersion.imageι ≫ c.toBase = j := by
  rw [Scheme.Hom.toImage_imageι_assoc, show c.immersion ≫ c.toBase = _ from Over.w c.obj.hom]
  rfl

/-- **The scheme-theoretic closure of `U` in a compactification**, as a compactification of `U`
over `X`: the open immersion `U ⟶ Z` into the scheme-theoretic image `Z` of `j'`, with the proper
structure morphism `Z ⟶ X' ⟶ X`. -/
public def CompactificationOf.closure : CompactificationOf (Over.mk j) :=
  ⟨StructuredArrow.mk (Y := Over.mk (c.immersion.imageι ≫ c.toBase))
    (Over.homMk (U := Over.mk j) c.immersion.toImage (c.toImage_imageι_toBase j)),
    ⟨inferInstanceAs (IsOpenImmersion c.immersion.toImage),
      inferInstanceAs (IsProper (c.immersion.imageι ≫ c.toBase))⟩⟩

/-- The closed immersion of the scheme-theoretic closure into the compactification, as a
morphism of compactifications. -/
public def CompactificationOf.closureHom : c.closure j ⟶ c :=
  ObjectProperty.homMk (StructuredArrow.homMk (Over.homMk c.immersion.imageι rfl) (by
    ext
    exact c.immersion.toImage_imageι))

/-- `X` itself, as the trivial compactification of `U` over `X`. -/
public def trivialCompactification : CompactificationOf (Over.mk j) :=
  ⟨StructuredArrow.mk (Y := Over.mk (𝟙 X)) (Over.homMk (U := Over.mk j) j (Category.comp_id j)),
    ⟨inferInstanceAs (IsOpenImmersion j), inferInstanceAs (IsProper (𝟙 X))⟩⟩

/-- The structure morphism of the scheme-theoretic closure, as a morphism to the trivial
compactification. -/
public def CompactificationOf.closureToTrivial : c.closure j ⟶ trivialCompactification j :=
  ObjectProperty.homMk (StructuredArrow.homMk (Over.homMk (c.immersion.imageι ≫ c.toBase)
    (Category.comp_id _)) (by
      ext
      exact c.toImage_imageι_toBase j))

/-- The interior of the scheme-theoretic closure is dense. -/
public lemma CompactificationOf.denseRange_closure :
    DenseRange (c.closure j).immersion.base :=
  c.immersion.toImage.denseRange

/-- **Stacks Project, Tag 0G4X.** Let `j : U ⟶ X` be an open immersion of Noetherian schemes and
let `j' : U ⟶ X'` be a compactification of `U` over `X`, with structure morphism `f : X' ⟶ X`
(`f` proper, `j'` an open immersion and `j = f ∘ j'`). Then there is a canonical isomorphism

`Rj_! ≅ Rf_* ∘ R(j')_!`

of functors `D^b_{Coh}(𝒪_U) ⥤ Pro-D^b_{Coh}(𝒪_X)`, where `Rj_!` and `R(j')_!` are the extensions
by zero of [Stacks, Tag 0G4N] and `Rf_*` acts on pro-objects termwise.

The proof is the source's. Let `X'' ⊆ X'` be the scheme-theoretic closure of `j'`, with
`j'' : U ⟶ X''` and `f' : X'' ⟶ X'` (`AlgebraicGeometry.CompactificationOf.closure`). As `U` is
dense in `X''`, [Stacks, Tag 0ATU] (c) gives `j''(U) = f'⁻¹(j'(U)) = (f ∘ f')⁻¹(j(U))`, so the case
`AlgebraicGeometry.compactificationShriekOfPreimage` of [Stacks, Tag 0G4W] gives
`Rf'_* ∘ Rj''_! ≅ Rj'_!` and `R(f ∘ f')_* ∘ Rj''_! ≅ Rj_!`; and `R(f ∘ f')_* ≅ Rf_* ∘ Rf'_*`
(`AlgebraicGeometry.properPushforwardBoundedCoherentCompIso`). -/
@[stacks 0G4X]
public def extensionByZeroCompactificationIso :
    extensionByZeroOpenImmersion j ≅
      extensionByZeroOpenImmersion c.immersion ⋙
        ProSeq.map (properPushforwardBoundedCoherent c.toBase) :=
  have hd := c.denseRange_closure j
  have h₁ := CompactificationOf.preservesInterior_of_denseRange (c.closureToTrivial j) hd
  have h₂ := CompactificationOf.preservesInterior_of_denseRange (c.closureHom j) hd
  haveI : IsNoetherian c.immersion.image := CompactificationOf.isNoetherian_space (c.closure j)
  have hU₁ : (c.immersion.imageι ≫ c.toBase) ⁻¹ᵁ j.opensRange =
      c.immersion.toImage.opensRange := TopologicalSpace.Opens.ext h₁
  have hU₂ : c.immersion.imageι ⁻¹ᵁ c.immersion.opensRange =
      c.immersion.toImage.opensRange := TopologicalSpace.Opens.ext h₂
  compactificationShriekOfPreimage j c.immersion.toImage (c.immersion.imageι ≫ c.toBase)
      (c.toImage_imageι_toBase j) hU₁ ≪≫
    Functor.isoWhiskerLeft (extensionByZeroOpenImmersion c.immersion.toImage)
      (ProSeq.mapIsoOfIso
          (properPushforwardBoundedCoherentCompIso c.immersion.imageι c.toBase).symm ≪≫
        (ProSeq.mapComp (properPushforwardBoundedCoherent c.immersion.imageι)
          (properPushforwardBoundedCoherent c.toBase)).symm) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (compactificationShriekOfPreimage c.immersion c.immersion.toImage
      c.immersion.imageι c.immersion.toImage_imageι hU₂).symm _

end Closure

/-! ### Independence of the compactification -/

/-- A compactification `c` of `X₀` over `S` read as a compactification of `X₀` over a scheme `T`
through which its structure morphism factors: given `g : c.space ⟶ T` proper and an open
immersion `i : X₀.left ⟶ T` with `c.immersion ≫ g = i`. -/
@[sga "4 XVII 3.2.5"]
public def CompactificationOf.ofFactor {S T : Scheme.{u}} {X₀ : Over S} {Z : Scheme.{u}}
    (k : X₀.left ⟶ Z) [IsOpenImmersion k] (g : Z ⟶ T) [IsProper g] (i : X₀.left ⟶ T)
    (h : k ≫ g = i) : CompactificationOf (Over.mk i) :=
  ⟨StructuredArrow.mk (Y := Over.mk g) (Over.homMk (U := Over.mk i) k h),
    ⟨inferInstanceAs (IsOpenImmersion k), inferInstanceAs (IsProper g)⟩⟩

section FTS

variable {S : Scheme.{u}} [IsNoetherian S] {X₁ Y₁ : FTS S} (f : X₁ ⟶ Y₁)
  (c₁ c₂ : CompactificationOf (Over.mk f.left))

/-- The morphism `X ⟶ X̄₁ ×_Y X̄₂` into the fibre product of two compactifications. -/
public abbrev compactificationPairMap : X₁.left ⟶ pullback c₁.toBase c₂.toBase :=
  pullback.lift c₁.immersion c₂.immersion
    ((show c₁.immersion ≫ c₁.toBase = _ from Over.w c₁.obj.hom).trans
      (show c₂.immersion ≫ c₂.toBase = _ from Over.w c₂.obj.hom).symm)

/-- `X ⟶ X̄₁ ×_Y X̄₂` is an immersion: its composite with the first projection is the open
immersion `X ⟶ X̄₁`. -/
public instance isImmersion_compactificationPairMap :
    IsImmersion (compactificationPairMap f c₁ c₂) :=
  have : IsImmersion (compactificationPairMap f c₁ c₂ ≫ pullback.fst c₁.toBase c₂.toBase) := by
    rw [pullback.lift_fst]
    infer_instance
  IsImmersion.of_comp _ (pullback.fst c₁.toBase c₂.toBase)

/-- **A compactification factoring through another gives the same `Rf_!`.** Let `c` be a
compactification `j : X ⟶ X̄` of `X` over `Y`, and let `k : X ⟶ Z` be an open immersion and
`g : Z ⟶ X̄` proper with `g ∘ k = j`, so that `Z` with `p = f̄ ∘ g` is a further compactification.
Then

`Rf̄_* ∘ Rj_! ≅ Rf̄_* ∘ Rg_* ∘ Rk_! ≅ Rp_* ∘ Rk_!`,

the first isomorphism being [Stacks, Tag 0G4X] for `j` and its compactification `k`
(`AlgebraicGeometry.extensionByZeroCompactificationIso`), the second the composition isomorphism
of the derived direct image. -/
public def lowerShriekIsoOfFactor (c : CompactificationOf (Over.mk f.left)) {Z : Scheme.{u}}
    (k : X₁.left ⟶ Z) [IsOpenImmersion k] (g : Z ⟶ c.space) [IsProper g]
    (hk : k ≫ g = c.immersion) (p : Z ⟶ Y₁.left) [IsProper p] (hp : g ≫ c.toBase = p)
    (h : k ≫ p = f.left) :
    lowerShriek f c ≅ lowerShriek f (CompactificationOf.ofFactor k p f.left h) :=
  haveI : IsNoetherian Z :=
    CompactificationOf.isNoetherian_space (CompactificationOf.ofFactor k p f.left h)
  Functor.isoWhiskerRight
      (extensionByZeroCompactificationIso c.immersion
        (CompactificationOf.ofFactor k g c.immersion hk)) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (extensionByZeroOpenImmersion k)
      (ProSeq.mapComp (properPushforwardBoundedCoherent g)
          (properPushforwardBoundedCoherent c.toBase) ≪≫
        ProSeq.mapIsoOfIso (properPushforwardBoundedCoherentCompIso g c.toBase ≪≫
          properPushforwardBoundedCoherentCongr hp))

/-- **Stacks Project, Tag 0G50.** In Situation [Stacks, Tag 0F42] let `f : X ⟶ Y` be a morphism
of `FTS_S`. The functor `Rf_! = Rf̄_* ∘ Rj_!` of [Stacks, Section 0G4Z]
(`AlgebraicGeometry.lowerShriek`) is, up to isomorphism, independent of the choice of the
compactification `j : X ⟶ X̄` of `X` over `Y`.

The proof is the source's. Two compactifications `X̄₁`, `X̄₂` are dominated by a third, the
scheme-theoretic closure `X̄₃` of `X` in `X̄₁ ×_Y X̄₂`
(the closure of `AlgebraicGeometry.compactificationPairMap`; that `X ⟶ X̄₃` is an open immersion is
because `X ⟶ X̄₁ ×_Y X̄₂` is a quasi-compact immersion), which is cofilteredness of the category of
compactifications for these two objects; and a morphism `g : X̄₃ ⟶ X̄ᵢ` of compactifications gives
`Rf̄ᵢ_* ∘ Rjᵢ_! ≅ Rf̄ᵢ_* ∘ Rg_* ∘ Rj₃_! ≅ Rf̄₃_* ∘ Rj₃_!` by [Stacks, Tag 0G4X]
(`AlgebraicGeometry.lowerShriekIsoOfFactor`). -/
@[stacks 0G50]
public def lowerShriekIso : lowerShriek f c₁ ≅ lowerShriek f c₂ :=
  have h : (compactificationPairMap f c₁ c₂).toImage ≫ (compactificationPairMap f c₁ c₂).imageι ≫
      pullback.fst c₁.toBase c₂.toBase ≫ c₁.toBase = f.left := by
    rw [Scheme.Hom.toImage_imageι_assoc, pullback.lift_fst_assoc]
    exact show c₁.immersion ≫ c₁.toBase = _ from Over.w c₁.obj.hom
  lowerShriekIsoOfFactor f c₁ (compactificationPairMap f c₁ c₂).toImage
      ((compactificationPairMap f c₁ c₂).imageι ≫ pullback.fst c₁.toBase c₂.toBase)
      (by rw [Scheme.Hom.toImage_imageι_assoc, pullback.lift_fst])
      ((compactificationPairMap f c₁ c₂).imageι ≫ pullback.fst c₁.toBase c₂.toBase ≫ c₁.toBase)
      (Category.assoc _ _ _) h ≪≫
    (lowerShriekIsoOfFactor f c₂ (compactificationPairMap f c₁ c₂).toImage
      ((compactificationPairMap f c₁ c₂).imageι ≫ pullback.snd c₁.toBase c₂.toBase)
      (by rw [Scheme.Hom.toImage_imageι_assoc, pullback.lift_snd])
      ((compactificationPairMap f c₁ c₂).imageι ≫ pullback.fst c₁.toBase c₂.toBase ≫ c₁.toBase)
      (by rw [Category.assoc, ← pullback.condition]) h).symm

end FTS

end AlgebraicGeometry
