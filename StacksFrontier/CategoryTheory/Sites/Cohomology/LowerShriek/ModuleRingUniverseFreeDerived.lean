module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DirectImageFullyFaithful
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LowerShriek
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.VanishingAlongAFunctorEssentiallySmall
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.DerivedAdjunction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.ModuleRingUniverseFree
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 07AC and the last assertion of 07AS, with the module universe free of the ring universe

Let `u : C ⥤ D` be a continuous and cocontinuous functor of sites, let `O_D` be a sheaf of rings
on `D` with sections in `Type r`, and set `O_C = g^{-1} O_D`.  This file develops the derived
lower-shriek functor `Lg_! : D(O_C) ⟶ D(O_D)` on sheaves of modules, together with the derived
adjunction `Lg_! ⊣ g^*` and the identity `g^* ∘ Lg_! = id`, with the universe `m` of the module
sections independent of the universe `r` of the ring sections.

## Relation to `DerivedAdjunction.lean`

`StacksFrontier/CategoryTheory/Sites/Cohomology/LowerShriek/DerivedAdjunction.lean` takes `O_D` in
`Sheaf K RingCat.{w}` and the modules in `SheafOfModules.{w}`: one universe for both.  That
cannot be specialised to the lisse-étale and flat-fppf sites of **Stacks 0787**: their objects lie
in `Type (u+1)` and their morphisms in `Type u`, so the Čech computation of **Stacks 0D6X**
forces the module sections into `Type (u+1)`, whereas the structure sheaf of **Stacks 06TV** has
its sections in `Type u`.  Lifting the structure sheaf is not an option — that would state the
lemma about a different, merely equivalent, category of modules.

The declarations of the section `TwoSites` below are the **generalization** of those of
`DerivedAdjunction.lean` in which the two universes are separated: at `m = r = w` they *are*
the declarations there, by `rfl` — `restrictionModules`, `lowerShriekModules`,
`adjunctionModules` and `derivedLowerShriekAdjunction` unfold to the very same terms, the
structure map `Stacks.SheafOfModules.structureMap` being
`Stacks.Cohomology.DerivedLowerShriek.idRingMap`
at a free ring universe, and their instance hypotheses are those of `DerivedAdjunction.lean`.
The declarations that need the generators `j_{U!} O_U` — the acyclicity statement and the two
inputs of the derived adjunction it supplies — are stated at the module universe
`max u₁ u₂ v₁ v₂ r t`, which is where the generators live; see `ModuleRingUniverseFree.lean`.

## Main definitions

All in the namespace `Stacks.Cohomology.DerivedLowerShriek.FreeRingUniverse`.

* `restrictionModules`, `lowerShriekModules`, `adjunctionModules`: `g^*`, `g_!` and the ordinary
  adjunction `g_! ⊣ g^*` on sheaves of modules.  These are Mathlib's
  `SheafOfModules.pushforward`, `SheafOfModules.pullback` and
  `SheafOfModules.pullbackPushforwardAdjunction` at the identity structure map of `g^{-1} O_D`,
  and agree with `Stacks.SheafOfModules.inverseImage` and
  `Stacks.SheafOfModules.lowerShriekAdjunction` of **Stacks 0797**.
* `derivedRestriction`, `derivedLowerShriek`, `derivedLowerShriekComparison`: derived restriction
  and the total left derived lower-shriek functor `Lg_!` with its counit.
* `derivedLowerShriekAdjunction`: **Stacks 07AC**, the derived adjunction `Lg_! ⊣ g^*`.
* `derivedLowerShriekRestrictionIso`: the last assertion of **Stacks 07AS** parts (2) and (4),
  `g^* ∘ Lg_! ≅ 𝟭`.

## Main results

* `lowerShriekModules_acyclic_of_abelian`: the acyclicity statement of **Stacks 07AC** for
  modules, from the object-level vanishing of **Stacks 0D6X** on underlying abelian sheaves.
* `subsingleton_ext_restrictionModules_toSheaf` and `lowerShriekModules_acyclic_of_cech`: that
  vanishing supplied from Čech data, so the acyclicity statement carries no vanishing
  hypothesis.
* `hasPointwiseLeftDerivedLowerShriek_of_acyclic` and
  `isLeftDerivedFunctor_derivedLowerShriek_comp_of_acyclic`: the two inputs of the derived
  adjunction, reduced to that acyclicity statement.
* `isIso_adjunctionModules_unit`: `g^* g_! = id` for a fully faithful functor of sites, which is
  **Stacks 077I**, and `isIso_derivedLowerShriekAdjunction_unit`: hence `g^* Lg_! = id`.

## Implementation notes

`Stacks.Cohomology.SiteModules.moduleSheavesAbelian` and its two companions are switched off, as
in `StacksFrontier/CategoryTheory/Sites/Cohomology/LowerShriek/ModuleRingUniverseFree.lean`; see the
implementation notes there.

The derived adjunction is `Stacks.Cohomology.UnboundedComplexes.derivedAdjunction`, Stacks 09T5
with absoluteness of the right derived functor already discharged from Grothendieck abelianness.
As in `DerivedAdjunction.lean`, whatever Mathlib supplies only for a small site is carried as an
instance hypothesis: sheafification of abelian sheaves at the module universe, existence of the
left adjoint of restriction of modules, `EnoughInjectives`, `HasExt`, and
`IsGrothendieckAbelian` of `Mod(O_D)`.  Each of these is available at the lisse-étale and
flat-fppf sites, which is the point of the file.

## References

* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
* [Stacks Project, Tag 07AC](https://stacks.math.columbia.edu/tag/07AC)
* [Stacks Project, Tag 07AS](https://stacks.math.columbia.edu/tag/07AS)
* [Stacks Project, Tag 077I](https://stacks.math.columbia.edu/tag/077I)
* [Stacks Project, Tag 0787](https://stacks.math.columbia.edu/tag/0787)
* [Stacks Project, Tag 0794](https://stacks.math.columbia.edu/tag/0794)
* [Stacks Project, Tag 0797](https://stacks.math.columbia.edu/tag/0797)
* [Stacks Project, Tag 09T5](https://stacks.math.columbia.edu/tag/09T5)
* [Stacks Project, Tag 0D6X](https://stacks.math.columbia.edu/tag/0D6X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Abelian

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives

universe m t r v₁ u₁ v₂ u₂

namespace Stacks.Cohomology.DerivedLowerShriek.FreeRingUniverse

/-! ### Exactness of `ℕ`-indexed colimits, with the ring universe free -/

/-- `ℕ`-indexed colimits of presheaves of modules are exact, with the universe of the sections
of the presheaf of rings independent of the universe of the module sections.  They are computed
on underlying presheaves of abelian groups, where exactness is Grothendieck's AB5 applied
objectwise.

This is `Stacks.Cohomology.DerivedLowerShriek.hasExactColimitsOfShape_nat_presheafOfModules`
with the two universes split. -/
theorem hasExactColimitsOfShape_nat_presheafOfModules {E : Type u₁} [Category.{v₁} E]
    (S : Eᵒᵖ ⥤ RingCat.{r}) : HasExactColimitsOfShape ℕ (PresheafOfModules.{m} S) :=
  have := hasExactColimitsOfShape_nat_addCommGrpCat.{m}
  ⟨⟨fun _ _ _ => ⟨fun {F} =>
    have : PreservesLimit F (colim (J := ℕ) ⋙ PresheafOfModules.toPresheaf S) :=
      preservesLimit_of_natIso _ (preservesColimitNatIso (PresheafOfModules.toPresheaf S)).symm
    preservesLimit_of_reflects_of_preserves _ (PresheafOfModules.toPresheaf S)⟩⟩⟩

/-- `ℕ`-indexed colimits of sheaves of modules are exact, with the ring universe independent of
the module universe: they are computed from those of presheaves of modules, which are exact, by
the sheafification adjunction, whose left adjoint is exact.

This is `Stacks.Cohomology.DerivedLowerShriek.hasExactColimitsOfShape_nat` with the two
universes split. -/
theorem hasExactColimitsOfShape_nat {E : Type u₁} [Category.{v₁} E]
    {L : GrothendieckTopology E} (T : Sheaf L RingCat.{r})
    [HasWeakSheafify L AddCommGrpCat.{m}] [L.WEqualsLocallyBijective AddCommGrpCat.{m}]
    [HasSheafify L AddCommGrpCat.{m}] :
    HasExactColimitsOfShape ℕ (SheafOfModules.{m} T) :=
  have := hasExactColimitsOfShape_nat_presheafOfModules.{m} (E := E) T.obj
  (PresheafOfModules.sheafificationAdjunction (𝟙 T.obj)).hasExactColimitsOfShape ℕ

/-! ### The two sites, at an arbitrary module universe -/

section TwoSites

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (f : C ⥤ D) [f.IsContinuous J K] [f.IsCocontinuous J K] (O : Sheaf K RingCat.{r})
  [HasWeakSheafify J AddCommGrpCat.{m}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
  [HasWeakSheafify K AddCommGrpCat.{m}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{m}]
  [(SheafOfModules.pushforward.{m} (F := f)
    (Stacks.SheafOfModules.structureMap J K f O)).IsRightAdjoint]

/-- `g^* = g^{-1} : Mod(O_D) ⥤ Mod(O_C)`, restriction of sheaves of modules along the functor of
sites, with the sections of `O_D` in a universe independent of the module sections.  This is
`Stacks.SheafOfModules.inverseImage` of **Stacks 0797**; at `m = r` it is
`Stacks.Cohomology.DerivedLowerShriek.restrictionModules`. -/
abbrev restrictionModules :
    SheafOfModules.{m} O ⥤
      SheafOfModules.{m} (Stacks.SheafOfModules.inverseImageRing J K f O) :=
  SheafOfModules.pushforward.{m} (Stacks.SheafOfModules.structureMap J K f O)

/-- `g_! : Mod(O_C) ⥤ Mod(O_D)`, the left adjoint of restriction of modules, with the ring
universe free of the module universe.  At `m = r` it is
`Stacks.Cohomology.DerivedLowerShriek.lowerShriekModules`. -/
abbrev lowerShriekModules :
    SheafOfModules.{m} (Stacks.SheafOfModules.inverseImageRing J K f O) ⥤
      SheafOfModules.{m} O :=
  SheafOfModules.pullback.{m} (Stacks.SheafOfModules.structureMap J K f O)

/-- The ordinary adjunction `g_! ⊣ g^*` between lower shriek and restriction of sheaves of
modules, with the ring universe free of the module universe.  It is the adjunction of
**Stacks 0797**; at `m = r` it is `Stacks.Cohomology.DerivedLowerShriek.adjunctionModules`. -/
abbrev adjunctionModules :
    lowerShriekModules.{m} J K f O ⊣ restrictionModules.{m} J K f O :=
  SheafOfModules.pullbackPushforwardAdjunction.{m}
    (Stacks.SheafOfModules.structureMap J K f O)

/-- Restriction of sheaves of modules along a continuous and cocontinuous functor of sites
preserves finite colimits: it preserves every colimit indexed in the universe of the module
sections, by `Stacks.SheafOfModules.pushforward_preservesColimits`, whose ring universe is
already free. -/
instance preservesFiniteColimits_restriction :
    PreservesFiniteColimits (restrictionModules.{m} J K f O) := by
  have h : PreservesColimitsOfSize.{m, m}
      (restrictionModules.{m} J K f O) :=
    Stacks.SheafOfModules.pushforward_preservesColimits f _
  exact PreservesColimitsOfSize.preservesFiniteColimits.{m, m} _

omit [(SheafOfModules.pushforward.{m} (F := f)
    (Stacks.SheafOfModules.structureMap J K f O)).IsRightAdjoint] in
/-- **Restriction of sheaves of modules along a continuous and cocontinuous functor of sites is
exact**, with the ring universe free of the module universe.  Left exactness holds because
restriction is the right adjoint of the lower-shriek functor; right exactness is cocontinuity of
the functor of sites, through the fact that restriction commutes with sheafification. -/
@[sga "4 IV 11.2.2" "more general"]
theorem restriction_exact :
    exactFunctor (SheafOfModules.{m} O)
      (SheafOfModules.{m} (Stacks.SheafOfModules.inverseImageRing J K f O))
      (restrictionModules.{m} J K f O) :=
  ⟨inferInstanceAs (PreservesFiniteLimits (restrictionModules.{m} J K f O)),
    preservesFiniteColimits_restriction.{m} J K f O⟩

/-- Restriction of sheaves of modules is additive, being exact. -/
instance additive_restriction : (restrictionModules.{m} J K f O).Additive :=
  exactFunctor_le_additiveFunctor _ _ _ (restriction_exact.{m} J K f O)

/-- The lower-shriek functor is additive, being a left adjoint between additive categories. -/
instance additive_lowerShriek : (lowerShriekModules.{m} J K f O).Additive := by
  let F := lowerShriekModules.{m} J K f O
  let : PreservesBinaryBiproducts F := preservesBinaryBiproducts_of_preservesBinaryCoproducts F
  exact Functor.additive_of_preservesBinaryBiproducts F

/-! ### Existence and absoluteness of `Lg_!` -/

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- Lower shriek applied degreewise to unbounded homotopy categories. -/
abbrev lowerShriekOnHomotopy :
    HomotopyCategory (SheafOfModules.{m}
        (Stacks.SheafOfModules.inverseImageRing J K f O)) (ComplexShape.up ℤ) ⥤
      HomotopyCategory (SheafOfModules.{m} O) (ComplexShape.up ℤ) :=
  (lowerShriekModules.{m} J K f O).mapHomotopyCategory (ComplexShape.up ℤ)

/-- Restriction applied degreewise to unbounded homotopy categories. -/
abbrev restrictionOnHomotopy :
    HomotopyCategory (SheafOfModules.{m} O) (ComplexShape.up ℤ) ⥤
      HomotopyCategory (SheafOfModules.{m}
        (Stacks.SheafOfModules.inverseImageRing J K f O)) (ComplexShape.up ℤ) :=
  (restrictionModules.{m} J K f O).mapHomotopyCategory (ComplexShape.up ℤ)

/-- The ordinary lower-shriek--restriction adjunction, read on the unbounded homotopy
categories. -/
abbrev homotopyAdjunction :
    lowerShriekOnHomotopy.{m} J K f O ⊣ restrictionOnHomotopy.{m} J K f O :=
  (adjunctionModules.{m} J K f O).mapHomotopyCategory (ComplexShape.up ℤ)

/-- Restriction of sheaves of modules, induced on the unbounded derived categories by
exactness. -/
abbrev derivedRestriction :
    DerivedCategory (SheafOfModules.{m} O) ⥤
      DerivedCategory (SheafOfModules.{m}
        (Stacks.SheafOfModules.inverseImageRing J K f O)) :=
  (restrictionModules.{m} J K f O).mapDerivedCategory

/-- The comparison from degreewise restriction to restriction on the derived categories.  It is
an isomorphism, restriction being exact. -/
abbrev derivedRestrictionComparison :
    restrictionOnHomotopy.{m} J K f O ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ derivedRestriction.{m} J K f O :=
  (restrictionModules.{m} J K f O).mapDerivedCategoryFactorsh.inv

/-- Restriction on the derived categories is the right derived functor of degreewise
restriction, its comparison transformation being invertible. -/
@[sga "4½ Etat_0 4.1.3" "special case"]
instance isRightDerivedFunctor_derivedRestriction :
    (derivedRestriction.{m} J K f O).IsRightDerivedFunctor
      (derivedRestrictionComparison.{m} J K f O)
      (HomotopyCategory.quasiIso (SheafOfModules.{m} O)
        (ComplexShape.up ℤ)) :=
  Functor.isRightDerivedFunctor_of_inverts _ _
    ((restrictionModules.{m} J K f O).mapDerivedCategoryFactorsh)

/-- The quasi-isomorphisms of the unbounded homotopy category of `Mod(O_C)`, the class at which
the left derived functor of lower shriek is taken. -/
abbrev sourceQuasiIso :
    MorphismProperty
      (HomotopyCategory (SheafOfModules.{m}
        (Stacks.SheafOfModules.inverseImageRing J K f O)) (ComplexShape.up ℤ)) :=
  HomotopyCategory.quasiIso (SheafOfModules.{m}
    (Stacks.SheafOfModules.inverseImageRing J K f O)) (ComplexShape.up ℤ)

variable [(lowerShriekOnHomotopy.{m} J K f O ⋙ DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
  (sourceQuasiIso.{m} J K f O)]

/-- The canonical unbounded left derived lower-shriek functor `Lg_!`, with the ring universe free
of the module universe. -/
abbrev derivedLowerShriek :
    DerivedCategory (SheafOfModules.{m}
        (Stacks.SheafOfModules.inverseImageRing J K f O)) ⥤
      DerivedCategory (SheafOfModules.{m} O) :=
  (lowerShriekOnHomotopy.{m} J K f O ⋙ DerivedCategory.Qh).totalLeftDerived DerivedCategory.Qh
    (sourceQuasiIso.{m} J K f O)

/-- The comparison from derived lower shriek to degreewise lower shriek on the homotopy category,
i.e. the counit exhibiting `Lg_!` as a left derived functor. -/
abbrev derivedLowerShriekComparison :
    DerivedCategory.Qh ⋙ derivedLowerShriek.{m} J K f O ⟶
      lowerShriekOnHomotopy.{m} J K f O ⋙ DerivedCategory.Qh :=
  (lowerShriekOnHomotopy.{m} J K f O ⋙ DerivedCategory.Qh).totalLeftDerivedCounit
    DerivedCategory.Qh (sourceQuasiIso.{m} J K f O)

variable [IsGrothendieckAbelian.{m}
    (SheafOfModules.{m} O)]
  [(derivedLowerShriek.{m} J K f O ⋙ derivedRestriction.{m} J K f O).IsLeftDerivedFunctor
  ((Functor.associator DerivedCategory.Qh (derivedLowerShriek.{m} J K f O)
      (derivedRestriction.{m} J K f O)).inv ≫
    Functor.whiskerRight (derivedLowerShriekComparison.{m} J K f O)
      (derivedRestriction.{m} J K f O))
  (sourceQuasiIso.{m} J K f O)]

/-- **Stacks 07AC**, the derived adjunction, with the ring universe free of the module universe:
the unbounded left derived lower-shriek functor is left adjoint to derived restriction of sheaves
of modules.  This is **Stacks 09T5** on the unbounded derived category of the Grothendieck
abelian category `Mod(O_D)`. -/
def derivedLowerShriekAdjunction :
    derivedLowerShriek.{m} J K f O ⊣ derivedRestriction.{m} J K f O :=
  Stacks.Cohomology.UnboundedComplexes.derivedAdjunction (homotopyAdjunction.{m} J K f O)
    (sourceQuasiIso.{m} J K f O) (derivedLowerShriekComparison.{m} J K f O)
    (derivedRestrictionComparison.{m} J K f O)

/-- **The unit of the derived adjunction `Lg_! ⊣ g^*` on sheaves of modules is an isomorphism as
soon as the ordinary one is**, with the ring universe free of the module universe.  For a fully
faithful `u` the ordinary unit `M ⟶ g^* g_! M` is an isomorphism — that is **Stacks 077I** — and
then `g^* ∘ Lg_! = id` on the unbounded derived category, which is the last assertion of
**Stacks 07AS** parts (2) and (4).

The argument is uniqueness of left derived functors, as in
`Stacks.Cohomology.DerivedLowerShriek.isIso_derivedAbelianLowerShriekAdjunction_unit` for abelian
sheaves.  At `m = r = w` this is the statement for the derived adjunction of
`DerivedAdjunction.lean`. -/
theorem isIso_derivedLowerShriekAdjunction_unit
    (hunit : IsIso (adjunctionModules.{m} J K f O).unit) :
    IsIso (derivedLowerShriekAdjunction.{m} J K f O).unit := by
  have := hunit
  set A := SheafOfModules.{m}
    (Stacks.SheafOfModules.inverseImageRing J K f O) with hA
  set W := HomotopyCategory.quasiIso A (ComplexShape.up ℤ) with hW
  set Gh := lowerShriekOnHomotopy.{m} J K f O with hGh
  set Lg := derivedLowerShriek.{m} J K f O with hLg
  set Fd := derivedRestriction.{m} J K f O with hFd
  set α := derivedLowerShriekComparison.{m} J K f O with hα
  set β := derivedRestrictionComparison.{m} J K f O with hβ
  set adjh := homotopyAdjunction.{m} J K f O with hadjh
  have hadjhunit : ∀ X, IsIso (adjh.unit.app X) := by
    rintro ⟨X⟩
    let v := (NatTrans.mapHomologicalComplex (adjunctionModules.{m} J K f O).unit
      (ComplexShape.up ℤ)).app X
    have : ∀ n, IsIso (v.f n) := by
      intro n
      change IsIso ((adjunctionModules.{m} J K f O).unit.app (X.X n))
      infer_instance
    have : IsIso v := HomologicalComplex.Hom.isIso_of_components _
    change IsIso ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map v)
    infer_instance
  have : IsIso adjh.unit := NatIso.isIso_of_isIso_app _
  have : IsIso β := by rw [hβ]; infer_instance
  set ηcmp := DerivedCategory.Qh.rightUnitor.hom ≫ DerivedCategory.Qh.leftUnitor.inv ≫
    Functor.whiskerRight adjh.unit DerivedCategory.Qh ≫
    (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft Gh β ≫
    (Functor.associator _ _ _).inv with hηcmp
  have hiso : IsIso ηcmp := by rw [hηcmp]; infer_instance
  have hid : (𝟭 (DerivedCategory A)).IsLeftDerivedFunctor ηcmp W :=
    Functor.isLeftDerivedFunctor_of_inverts W (𝟭 (DerivedCategory A)) (asIso ηcmp)
  exact (Functor.isLeftDerivedFunctor_iff_isIso_leftDerivedLift (Lg ⋙ Fd)
    ((Functor.associator DerivedCategory.Qh Lg Fd).inv ≫ Functor.whiskerRight α Fd) W
    (𝟭 (DerivedCategory A)) ηcmp).mp hid

/-- **The last assertion of Stacks 07AS parts (2) and (4), with the ring universe free of the
module universe**: restriction of modules after derived lower shriek is canonically the identity
of `D(O_C)`, whenever the ordinary unit is an isomorphism (**Stacks 077I**). -/
def derivedLowerShriekRestrictionIso (hunit : IsIso (adjunctionModules.{m} J K f O).unit) :
    derivedLowerShriek.{m} J K f O ⋙ derivedRestriction.{m} J K f O ≅
      𝟭 (DerivedCategory (SheafOfModules.{m}
        (Stacks.SheafOfModules.inverseImageRing J K f O))) :=
  have := isIso_derivedLowerShriekAdjunction_unit.{m} J K f O hunit
  (asIso (derivedLowerShriekAdjunction.{m} J K f O).unit).symm

end Derived

end TwoSites

/-! ### The generators `j_{U!} O_U`, at the module universe `max u₁ u₂ v₁ v₂ r t` -/

section Generators

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (f : C ⥤ D) [f.IsContinuous J K] [f.IsCocontinuous J K] (O : Sheaf K RingCat.{r})

variable [HasSheafify J AddCommGrpCat.{max u₁ u₂ v₁ v₂ r t}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u₁ u₂ v₁ v₂ r t}]
  [HasSheafify K AddCommGrpCat.{max u₁ u₂ v₁ v₂ r t}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{max u₁ u₂ v₁ v₂ r t}]
  [(SheafOfModules.pushforward.{max u₁ u₂ v₁ v₂ r t} (F := f)
    (Stacks.SheafOfModules.structureMap J K f O)).IsRightAdjoint]

/-! ### The acyclicity statement of Stacks 07AC -/

section Acyclicity

variable [EnoughInjectives (SheafOfModules.{max u₁ u₂ v₁ v₂ r t}
    (Stacks.SheafOfModules.inverseImageRing J K f O))]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{max u₁ u₂ v₁ v₂ r t})]
  [HasExt.{max u₁ u₂ v₁ v₂ r t} (SheafOfModules.{max u₁ u₂ v₁ v₂ r t}
    (Stacks.SheafOfModules.inverseImageRing J K f O))]
  [HasExt.{max u₁ u₂ v₁ v₂ r t} (Sheaf J AddCommGrpCat.{max u₁ u₂ v₁ v₂ r t})]

omit [f.IsCocontinuous J K] [HasSheafify K AddCommGrpCat.{max u₁ u₂ v₁ v₂ r t}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{max u₁ u₂ v₁ v₂ r t}] in
/-- **The generators `j_{U!} O_U` are `Ext`-acyclic for `g_! ⊣ g^*`**, granted the object-level
vanishing of **Stacks 0D6X** on the underlying abelian sheaves: for an injective `O_D`-module `I`
and an object `U` of `C`, `Ext^n_{Ab(C)}(j_{U!} ℤ_U, g^{-1} I) = 0` for `n ≥ 1`. -/
theorem extAcyclic_extensionByZeroUnit_of_abelian (U : C)
    (hExt : ∀ (I : SheafOfModules.{max u₁ u₂ v₁ v₂ r t} O), Injective I → ∀ n : ℕ, 0 < n →
      Subsingleton (Ext.{max u₁ u₂ v₁ v₂ r t}
        (extensionByZeroUnitAb.{max u₁ u₂ v₁ v₂ r t} J U)
        ((SheafOfModules.toSheaf (Stacks.SheafOfModules.inverseImageRing J K f O)).obj
          ((restrictionModules.{max u₁ u₂ v₁ v₂ r t} J K f O).obj I)) n)) :
    (adjunctionModules.{max u₁ u₂ v₁ v₂ r t} J K f O).extAcyclic
      (Stacks.SheafOfModules.extensionByZeroUnit.{u₁, v₁, r, max u₂ v₂ t}
        (Stacks.SheafOfModules.inverseImageRing J K f O) U) :=
  fun I hI n hn =>
    subsingleton_ext_extensionByZeroUnit_of_abelian.{max u₂ v₂ t} J
      (Stacks.SheafOfModules.inverseImageRing J K f O) U
      ((restrictionModules.{max u₁ u₂ v₁ v₂ r t} J K f O).obj I) (fun p hp => hExt I hI p hp) n hn

omit [f.IsCocontinuous J K] in
/-- **The acyclicity statement of Stacks 07AC for modules**, with the ring universe free of the
module universe, granted the object-level vanishing of **Stacks 0D6X** on the underlying abelian
sheaves.  The lower-shriek functor `g_! : Mod(O_C) ⥤ Mod(O_D)` carries every bounded above
acyclic complex whose terms are direct sums of the generators `j_{U!} O_U` to an acyclic
complex.

This is the single input of
`...FreeRingUniverse.hasPointwiseLeftDerivedLowerShriek_of_acyclic` and of
`...FreeRingUniverse.isLeftDerivedFunctor_derivedLowerShriek_comp_of_acyclic`, so with it the
whole of **Stacks 07AC** is available at these universes. -/
theorem lowerShriekModules_acyclic_of_abelian
    (hExt : ∀ (U : C) (I : SheafOfModules.{max u₁ u₂ v₁ v₂ r t} O), Injective I →
      ∀ n : ℕ, 0 < n →
      Subsingleton (Ext.{max u₁ u₂ v₁ v₂ r t}
        (extensionByZeroUnitAb.{max u₁ u₂ v₁ v₂ r t} J U)
        ((SheafOfModules.toSheaf (Stacks.SheafOfModules.inverseImageRing J K f O)).obj
          ((restrictionModules.{max u₁ u₂ v₁ v₂ r t} J K f O).obj I)) n))
    (a : ℤ)
    (L : CochainComplex (SheafOfModules.{max u₁ u₂ v₁ v₂ r t}
      (Stacks.SheafOfModules.inverseImageRing J K f O)) ℤ)
    (hLE : L.IsStrictlyLE a)
    (hLP : ∀ n, IsSumOfExtensionByZeroUnits.{max u₂ v₂ t} J
      (Stacks.SheafOfModules.inverseImageRing J K f O) (L.X n))
    (hLac : L.Acyclic) :
    (((lowerShriekModules.{max u₁ u₂ v₁ v₂ r t} J K f O).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj L).Acyclic := by
  refine (adjunctionModules.{max u₁ u₂ v₁ v₂ r t} J K f O).map_acyclic_of_extAcyclic L a hLac
    fun n => ?_
  obtain ⟨ι, U, ⟨e⟩⟩ := hLP n
  exact (adjunctionModules.{max u₁ u₂ v₁ v₂ r t} J K f O).extAcyclic_of_iso e
    ((adjunctionModules.{max u₁ u₂ v₁ v₂ r t} J K f O).extAcyclic_coproduct _
      fun i => extAcyclic_extensionByZeroUnit_of_abelian.{t} J K f O (U i) (hExt (U i)))

end Acyclicity

/-! ### Existence and absoluteness of `Lg_!` from the acyclicity statement -/

section Derived

attribute [local instance] HasDerivedCategory.standard

omit [f.IsCocontinuous J K] in
/-- **Stacks 07AC, existence**, with the ring universe free of the module universe, conditional
on its one remaining input.  If the lower-shriek functor carries every bounded above acyclic
complex whose terms are direct sums of the generators `j_{U!} O_U` to an acyclic complex, then it
has an unbounded left derived functor.

Every other hypothesis of the criterion of **Stacks 0794** holds here, with the class of objects
taken to be `...FreeRingUniverse.IsSumOfExtensionByZeroUnits`: that class contains a zero
object, is closed under binary direct sums and generates, `ℕ`-indexed colimits exist and are
exact in both categories, and the lower-shriek functor is additive and commutes with all
colimits, being a left adjoint. -/
theorem hasPointwiseLeftDerivedLowerShriek_of_acyclic
    (hFP : ∀ (a : ℤ) (L : CochainComplex (SheafOfModules.{max u₁ u₂ v₁ v₂ r t}
        (Stacks.SheafOfModules.inverseImageRing J K f O)) ℤ),
      L.IsStrictlyLE a →
      (∀ n, IsSumOfExtensionByZeroUnits.{max u₂ v₂ t} J
        (Stacks.SheafOfModules.inverseImageRing J K f O) (L.X n)) → L.Acyclic →
      (((lowerShriekModules.{max u₁ u₂ v₁ v₂ r t} J K f O).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj L).Acyclic) :
    (lowerShriekOnHomotopy.{max u₁ u₂ v₁ v₂ r t} J K f O ⋙
      DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
        (sourceQuasiIso.{max u₁ u₂ v₁ v₂ r t} J K f O) := by
  have := hasExactColimitsOfShape_nat.{max u₁ u₂ v₁ v₂ r t}
    (Stacks.SheafOfModules.inverseImageRing J K f O)
  have := hasExactColimitsOfShape_nat.{max u₁ u₂ v₁ v₂ r t} O
  exact CategoryTheory.Functor.hasPointwiseLeftDerivedFunctor_of_acyclic_mapHomologicalComplex
    (lowerShriekModules.{max u₁ u₂ v₁ v₂ r t} J K f O)
    (IsSumOfExtensionByZeroUnits.{max u₂ v₂ t} J
      (Stacks.SheafOfModules.inverseImageRing J K f O))
    (fun _ _ => isSumOfExtensionByZeroUnits_biprod _ _)
    (fun M => exists_epi_isSumOfExtensionByZeroUnits _ _ M) hFP

variable [(lowerShriekOnHomotopy.{max u₁ u₂ v₁ v₂ r t} J K f O ⋙
    DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
  (sourceQuasiIso.{max u₁ u₂ v₁ v₂ r t} J K f O)]

omit [f.IsCocontinuous J K] in
/-- **The derived lower-shriek functor is absolute**, with the ring universe free of the module
universe.  Under the acyclicity hypothesis of **Stacks 0794** for lower shriek, the left derived
functor `Lg_!` stays a left derived functor after composition with any functor out of `D(O_D)`,
because it is constructed by resolutions.  Taking `G` to be `derivedRestriction` is exactly the
second hypothesis of `derivedLowerShriekAdjunction` below. -/
theorem isLeftDerivedFunctor_derivedLowerShriek_comp_of_acyclic
    (hFP : ∀ (a : ℤ) (Lc : CochainComplex (SheafOfModules.{max u₁ u₂ v₁ v₂ r t}
        (Stacks.SheafOfModules.inverseImageRing J K f O)) ℤ),
      Lc.IsStrictlyLE a →
      (∀ n, IsSumOfExtensionByZeroUnits.{max u₂ v₂ t} J
        (Stacks.SheafOfModules.inverseImageRing J K f O) (Lc.X n)) → Lc.Acyclic →
      (((lowerShriekModules.{max u₁ u₂ v₁ v₂ r t} J K f O).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj Lc).Acyclic)
    {E : Type*} [Category E] (G : DerivedCategory (SheafOfModules.{max u₁ u₂ v₁ v₂ r t} O) ⥤ E) :
    (derivedLowerShriek.{max u₁ u₂ v₁ v₂ r t} J K f O ⋙ G).IsLeftDerivedFunctor
      ((Functor.associator DerivedCategory.Qh
          (derivedLowerShriek.{max u₁ u₂ v₁ v₂ r t} J K f O) G).inv ≫
        Functor.whiskerRight (derivedLowerShriekComparison.{max u₁ u₂ v₁ v₂ r t} J K f O) G)
      (sourceQuasiIso.{max u₁ u₂ v₁ v₂ r t} J K f O) := by
  have := hasExactColimitsOfShape_nat.{max u₁ u₂ v₁ v₂ r t}
    (Stacks.SheafOfModules.inverseImageRing J K f O)
  have := hasExactColimitsOfShape_nat.{max u₁ u₂ v₁ v₂ r t} O
  exact Functor.isLeftDerivedFunctor_comp_of_acyclic_mapHomologicalComplex
    (lowerShriekModules.{max u₁ u₂ v₁ v₂ r t} J K f O)
    (IsSumOfExtensionByZeroUnits.{max u₂ v₂ t} J
      (Stacks.SheafOfModules.inverseImageRing J K f O))
    (fun _ _ => isSumOfExtensionByZeroUnits_biprod _ _)
    (fun M => exists_epi_isSumOfExtensionByZeroUnits _ _ M) hFP DerivedCategory.Qh
    (derivedLowerShriek.{max u₁ u₂ v₁ v₂ r t} J K f O)
    (derivedLowerShriekComparison.{max u₁ u₂ v₁ v₂ r t} J K f O) G

end Derived

end Generators


/-! ### `g^* g_! = id` for a fully faithful functor of sites -/

section Unit

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (f : C ⥤ D) [f.IsContinuous J K] [f.IsCocontinuous J K] [f.Full] [f.Faithful]
  (O : Sheaf K RingCat.{r})
  [HasSheafify J AddCommGrpCat.{max u₁ u₂ v₁ v₂ r t}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u₁ u₂ v₁ v₂ r t}]
  [HasSheafify K AddCommGrpCat.{max u₁ u₂ v₁ v₂ r t}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{max u₁ u₂ v₁ v₂ r t}]
  [(SheafOfModules.pushforward.{max u₁ u₂ v₁ v₂ r t} (F := f)
    (Stacks.SheafOfModules.structureMap J K f O)).IsRightAdjoint]

omit [HasSheafify J AddCommGrpCat.{max u₁ u₂ v₁ v₂ r t}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u₁ u₂ v₁ v₂ r t}]
  [HasSheafify K AddCommGrpCat.{max u₁ u₂ v₁ v₂ r t}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{max u₁ u₂ v₁ v₂ r t}] in
/-- **`g^* g_! = id` on sheaves of modules, for a fully faithful functor of sites**, with the
ring universe free of the module universe.  The unit of the ordinary adjunction `g_! ⊣ g^*` is an
isomorphism as soon as the functor of sites is full and faithful.

This is `SheafOfModules.isIso_unit_of_isIso_coefficient` for the identity structure map of
`O_C = g^{-1} O_D`, which is trivially invertible; the content is the adjoint triple
`g_! ⊣ g^* ⊣ g_*` together with full faithfulness of the direct image.  That statement already
has the ring universe free of the module universe, so no new argument is needed here. -/
theorem isIso_adjunctionModules_unit :
    IsIso (adjunctionModules.{max u₁ u₂ v₁ v₂ r t} J K f O).unit :=
  SheafOfModules.isIso_unit_of_isIso_coefficient.{r, max u₂ v₁ r t, v₁, v₂, u₁, u₂}
    f J K O (Stacks.SheafOfModules.structureMap J K f O)
    (adjunctionModules.{max u₁ u₂ v₁ v₂ r t} J K f O)

end Unit

/-! ### Stacks 0D6X from Čech data, with the ring universe free -/

section ObjectVanishing

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (f : C ⥤ D) [f.IsContinuous J K]
  (Ocomm : Sheaf K CommRingCat.{r})
  [HasSheafify J AddCommGrpCat.{max u₁ u₂ v₁ v₂ r t}]
  [HasExt.{max u₁ u₂ v₁ v₂ r t} (Sheaf J AddCommGrpCat.{max u₁ u₂ v₁ v₂ r t})]
  (B : Set C)
  (Cov : ∀ U : C,
    Set { E : PreZeroHypercover.{max u₁ u₂ v₁ v₂ r t} U // E.sieve₀ ∈ J U })
  (hProducts : ∀ {U : C}
    (E : { E : PreZeroHypercover.{max u₁ u₂ v₁ v₂ r t} U // E.sieve₀ ∈ J U }),
    E ∈ Cov U → ∀ (p : ℕ) (i : Fin (p + 1) → E.1.I₀),
      HasProduct (fun a ↦ Over.mk (E.1.f (i a))))
  (hImageProducts : ∀ {U : C}
    (E : { E : PreZeroHypercover.{max u₁ u₂ v₁ v₂ r t} U // E.sieve₀ ∈ J U }),
    E ∈ Cov U → ∀ (p : ℕ) (i : Fin (p + 1) → (E.1.map f).I₀),
      HasProduct (fun a ↦ Over.mk ((E.1.map f).f (i a))))

/-- **Stacks 0D6X for an injective module, at the lower-shriek spellings and with the ring
universe free of the module universe.** Let `u : C ⥤ D` be a continuous functor of sites,
`g : Sh(C) → Sh(D)` the corresponding morphism of topoi, `O_D` a sheaf of rings on `D` whose
sections lie in `Type r`, and `I` an injective `O_D`-module with sections in
`Type (max u₁ u₂ v₁ v₂ r t)`.  Then the underlying abelian sheaf of `g^* I` has vanishing
positive-degree `Ext` out of `j_{U!} ℤ_U`, for every object `U` of the cofinal system of
coverings.

This is `Stacks.CechSite.injective_module_subsingleton_ext_of_functor`, whose ring universe is
already free, with its conclusion written at
`Stacks.Cohomology.DerivedLowerShriek.extensionByZeroUnitAb` and at
`...FreeRingUniverse.restrictionModules`, which is the form
`...FreeRingUniverse.lowerShriekModules_acyclic_of_abelian` consumes.  The two coefficient terms
agree because the underlying abelian sheaf of a restriction of modules is the restriction of the
underlying abelian sheaf, and the two generators agree once the covering-index universe is taken
to be the module universe.

The tag of Stacks 0D6X sits on
`Stacks.CechSite.injective_module_subsingleton_ext_of_functor`, which this restates; nothing is
registered here. -/
theorem subsingleton_ext_restrictionModules_toSheaf
    (hCovObjects : ∀ {U : C}
      (E : { E : PreZeroHypercover.{max u₁ u₂ v₁ v₂ r t} U // E.sieve₀ ∈ J U })
      (hE : E ∈ Cov U),
      U ∈ B ∧ (∀ i, E.1.X i ∈ B) ∧
        ∀ (p : ℕ) (i : Fin (p + 1) → E.1.I₀),
          letI : ∀ (q : ℕ) (j : Fin (q + 1) → E.1.I₀),
            HasProduct (fun a ↦ Over.mk (E.1.f (j a))) := hProducts E hE
          (∏ᶜ (fun a ↦ Over.mk (E.1.f (i a)))).left ∈ B)
    (hCovCofinal : ∀ U ∈ B, ∀ R ∈ J U,
      ∃ (E : { E : PreZeroHypercover.{max u₁ u₂ v₁ v₂ r t} U // E.sieve₀ ∈ J U }),
        E ∈ Cov U ∧ E.1.sieve₀ ≤ R)
    (hComparison : ∀ {U : C}
      (E : { E : PreZeroHypercover.{max u₁ u₂ v₁ v₂ r t} U // E.sieve₀ ∈ J U })
      (hE : E ∈ Cov U) (p : ℕ) (i : Fin (p + 1) → E.1.I₀),
        letI : ∀ (q : ℕ) (j : Fin (q + 1) → E.1.I₀),
          HasProduct (fun a ↦ Over.mk (E.1.f (j a))) := hProducts E hE
        letI : ∀ (q : ℕ) (j : Fin (q + 1) → (E.1.map f).I₀),
          HasProduct (fun a ↦ Over.mk ((E.1.map f).f (j a))) := hImageProducts E hE
        IsIso (Stacks.CechSite.cechProductMapOfFunctor f E.1 p i))
    (I : SheafOfModules.{max u₁ u₂ v₁ v₂ r t}
      (Stacks.SheafOfModules.Tensor.ringSheaf Ocomm)) [Injective I]
    (U : C) (hU : U ∈ B) (n : ℕ) (hn : 0 < n) :
    Subsingleton (Ext.{max u₁ u₂ v₁ v₂ r t}
      (extensionByZeroUnitAb.{max u₁ u₂ v₁ v₂ r t} J U)
      ((SheafOfModules.toSheaf (Stacks.SheafOfModules.inverseImageRing J K f
          (Stacks.SheafOfModules.Tensor.ringSheaf Ocomm))).obj
        ((restrictionModules.{max u₁ u₂ v₁ v₂ r t} J K f
          (Stacks.SheafOfModules.Tensor.ringSheaf Ocomm)).obj I)) n) :=
  Stacks.CechSite.injective_module_subsingleton_ext_of_functor.{max u₁ u₂ v₁ v₂ r t,
      max u₁ u₂ v₁ v₂ r t}
    { C := D, J := K, O := Ocomm } J f B Cov hProducts hImageProducts
    hCovObjects hCovCofinal hComparison I U hU n hn

section Acyclicity

variable [f.IsCocontinuous J K]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u₁ u₂ v₁ v₂ r t}]
  [HasSheafify K AddCommGrpCat.{max u₁ u₂ v₁ v₂ r t}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{max u₁ u₂ v₁ v₂ r t}]
  [(SheafOfModules.pushforward.{max u₁ u₂ v₁ v₂ r t} (F := f)
    (Stacks.SheafOfModules.structureMap J K f
      (Stacks.SheafOfModules.Tensor.ringSheaf Ocomm))).IsRightAdjoint]
  [EnoughInjectives (SheafOfModules.{max u₁ u₂ v₁ v₂ r t}
    (Stacks.SheafOfModules.inverseImageRing J K f
      (Stacks.SheafOfModules.Tensor.ringSheaf Ocomm)))]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{max u₁ u₂ v₁ v₂ r t})]
  [HasExt.{max u₁ u₂ v₁ v₂ r t} (SheafOfModules.{max u₁ u₂ v₁ v₂ r t}
    (Stacks.SheafOfModules.inverseImageRing J K f
      (Stacks.SheafOfModules.Tensor.ringSheaf Ocomm)))]

omit [f.IsCocontinuous J K] in
/-- **The acyclicity statement of Stacks 07AC for modules on two non-small sites, with the ring
universe free of the module universe and with no vanishing hypothesis.** The lower-shriek functor
`g_! : Mod(O_C) ⥤ Mod(O_D)` carries every bounded above acyclic complex whose terms are direct
sums of the generators `j_{U!} O_U` to an acyclic complex, granted the Čech data of
**Stacks 0D6X**: a cofinal system of coverings of every object, with the iterated fibre products
of its members and their preservation by the functor of sites.

This is `...FreeRingUniverse.lowerShriekModules_acyclic_of_abelian` with its one hypothesis
discharged by `...FreeRingUniverse.subsingleton_ext_restrictionModules_toSheaf`.  It is the
single input of `...FreeRingUniverse.hasPointwiseLeftDerivedLowerShriek_of_acyclic` and of
`...FreeRingUniverse.isLeftDerivedFunctor_derivedLowerShriek_comp_of_acyclic`, so with it the
whole of **Stacks 07AC** is available at these universes.  The tag of Stacks 07AC sits not here
but on the statements it is an input of. -/
theorem lowerShriekModules_acyclic_of_cech
    (hCovCofinal : ∀ (U : C), ∀ R ∈ J U,
      ∃ (E : { E : PreZeroHypercover.{max u₁ u₂ v₁ v₂ r t} U // E.sieve₀ ∈ J U }),
        E ∈ Cov U ∧ E.1.sieve₀ ≤ R)
    (hComparison : ∀ {U : C}
      (E : { E : PreZeroHypercover.{max u₁ u₂ v₁ v₂ r t} U // E.sieve₀ ∈ J U })
      (hE : E ∈ Cov U) (p : ℕ) (i : Fin (p + 1) → E.1.I₀),
        letI : ∀ (q : ℕ) (j : Fin (q + 1) → E.1.I₀),
          HasProduct (fun a ↦ Over.mk (E.1.f (j a))) := hProducts E hE
        letI : ∀ (q : ℕ) (j : Fin (q + 1) → (E.1.map f).I₀),
          HasProduct (fun a ↦ Over.mk ((E.1.map f).f (j a))) := hImageProducts E hE
        IsIso (Stacks.CechSite.cechProductMapOfFunctor f E.1 p i))
    (a : ℤ)
    (L : CochainComplex (SheafOfModules.{max u₁ u₂ v₁ v₂ r t}
      (Stacks.SheafOfModules.inverseImageRing J K f
        (Stacks.SheafOfModules.Tensor.ringSheaf Ocomm))) ℤ)
    (hLE : L.IsStrictlyLE a)
    (hLP : ∀ n, IsSumOfExtensionByZeroUnits.{max u₂ v₂ t} J
      (Stacks.SheafOfModules.inverseImageRing J K f
        (Stacks.SheafOfModules.Tensor.ringSheaf Ocomm)) (L.X n))
    (hLac : L.Acyclic) :
    (((lowerShriekModules.{max u₁ u₂ v₁ v₂ r t} J K f
        (Stacks.SheafOfModules.Tensor.ringSheaf Ocomm)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj L).Acyclic := by
  refine lowerShriekModules_acyclic_of_abelian.{t} J K f
    (Stacks.SheafOfModules.Tensor.ringSheaf Ocomm) ?_ a L hLE hLP hLac
  intro U I hI n hn
  have := hI
  exact subsingleton_ext_restrictionModules_toSheaf.{t} J K f Ocomm Set.univ Cov hProducts
    hImageProducts
    (fun _ _ => ⟨Set.mem_univ _, fun _ => Set.mem_univ _, fun _ _ => Set.mem_univ _⟩)
    (fun V _ R hR => hCovCofinal V R hR) hComparison I U (Set.mem_univ _) n hn

end Acyclicity

end ObjectVanishing

end Stacks.Cohomology.DerivedLowerShriek.FreeRingUniverse

end
