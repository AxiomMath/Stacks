module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyZero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.OpenClosedSequence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Restriction.CoefficientEquivalence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.StalkComparison
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekCompactSupportCompactification
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekProper
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleDenseSubsite
import StacksCore.Tactic.StacksAttribute

/-!
# The two zeroth compactly supported cohomology groups agree

Let `X` be a separated scheme of finite type over a field `k` and let `ℱ` be an abelian sheaf on
`X_étale`. Two groups `H⁰_c(X, ℱ)` are defined in the source: the group of sections with proper
support of Tag 0F72, and the zeroth cohomology of `RΓ_c(X, ℱ) = RΓ(Spec k, Rf_!ℱ)` of Tag 0GJZ.
Tag 0GK1 says they agree; both are `H⁰(X̄, j_!ℱ)` for a compactification `j : X ⟶ X̄`.

The two definitions are formalised on two presentations of the small étale site. Tag 0F72 is
`AlgebraicGeometry.SmallEtale.compactlySupportedSections`, on abelian sheaves on the site of
Tag 021B inside a big étale site `B`; Tag 0GJZ is
`Stacks.EtaleCohomology.compactlySupportedCohomologyGroup`, on sheaves of `ℤ`-modules on
Mathlib's small étale site `AlgebraicGeometry.Scheme.smallEtaleTopology`. An abelian sheaf is
read on both through `AlgebraicGeometry.SmallEtale.etaleModulesIntEquivalence`: forget the
`ℤ`-module structure and restrict to the site of Tag 021B.

## Main definitions

* `AlgebraicGeometry.SmallEtale.etaleModulesIntEquivalence`: sheaves of `ℤ`-modules on Mathlib's
  small étale site are abelian sheaves on the small étale site of Tag 021B.
* `AlgebraicGeometry.SmallEtale.etaleModulesIntEquivalenceExtensionByZeroIso`: extension by zero
  on the two presentations corresponds under that equivalence.
* `AlgebraicGeometry.SmallEtale.etaleModuleGlobalSectionsAddEquiv`: so do global sections.

## Main results

* `Stacks.EtaleCohomology.nonempty_addEquiv_compactlySupportedCohomologyGroup_zero`: **Tag
  0GK1**, the comparison itself.

## Implementation notes

The proof is the source's. For a compactification `j : X ⟶ X̄`, the group of Tag 0GJZ is
`Γ(X̄, j_!ℱ)` by `Stacks.EtaleCohomology.nonempty_compactlySupportedCohomologyGroup_zero_iso`, on
Mathlib's site; the group of Tag 0F72 is `Γ(X̄, j_!ℱ)` by Tag 0F75
(`AlgebraicGeometry.SmallEtale.compactlySupportedSections_extensionByZero`) and Tag 0F73
(`AlgebraicGeometry.SmallEtale.compactlySupportedSections_eq_top_of_isProper`), on the site of Tag
021B. The rest is the passage between the two sites: restriction along `j` is precomposition
with a functor of sites on both sides and those functors agree, so the left adjoints, extension
by zero, agree under the equivalence; and the final object of the bounded site is final in
Mathlib's.

Tag 0F75 needs `X̄` inside the big étale site `B`. When `X` is nonempty, `k` is no larger than a
stalk of `X`, so `Spec k` lies in `B`, and then so does `X̄`, being of finite type over `k` (Tag
000R). When `X` is empty, `X̄` need not lie in `B`, but then both groups are zero: every sheaf on
the small étale site of an empty scheme is zero, and so is its extension by zero.

The torsion hypothesis of the source is not used by its proof and is not assumed here.

## References

* [Stacks Project, Tag 0GK1](https://stacks.math.columbia.edu/tag/0GK1)
* [Stacks Project, Tag 0F75](https://stacks.math.columbia.edu/tag/0F75)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.SmallEtale

/-! ### The dictionary between the two presentations -/

section Dictionary

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Sheaves of `ℤ`-modules on Mathlib's small étale site are abelian sheaves on the small étale
site of Tag 021B.** The functor forgets the module structure and restricts along
`AlgebraicGeometry.SmallEtale.toEtaleSite`. -/
def etaleModulesIntEquivalence :
    Stacks.EtaleCohomology.EtaleModules.{u, 0} ℤ S ≌
      Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{u + 1} :=
  (Sheaf.coefficientEquivalence S.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).asEquivalence).trans
    (sheafEquiv B S hS AddCommGrpCat.{u + 1}).symm

/-- **Global sections correspond under the dictionary.** The final object of the bounded site is
final in Mathlib's site, and the functor of the dictionary does not change the group of sections
over it. -/
def etaleModuleGlobalSectionsAddEquiv (M : Stacks.EtaleCohomology.EtaleModules.{u, 0} ℤ S) :
    (Stacks.EtaleCohomology.etaleModuleGlobalSections.{u, 0} ℤ S).obj M ≃+
      ((etaleModulesIntEquivalence B S hS).functor.obj M).obj.obj
        (op (SmallEtale.final B S hS)) :=
  ((Sheaf.ΓNatIsoSheafSections S.smallEtaleTopology (ModuleCat.{u + 1} ℤ)
    (isTerminalToEtaleSiteFinal B S hS)).app M).toLinearEquiv.toAddEquiv

end Dictionary

/-! ### Restriction and extension by zero across the dictionary -/

section ExtensionByZero

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : SmallEtale B S hS)

/-- The structure morphism of an object of the small étale site of Tag 021B is étale, read as a
morphism of schemes. -/
instance etale_inclusion_map_obj_hom : Etale (B.inclusion.map U.obj.hom) := U.property

/-- Composition with the structure morphism of an object of the bounded site is continuous for
Mathlib's small étale topologies. This is `Scheme.Etale.smallEtaleCompose_isContinuous`, restated
with the source category spelled through the object, which is the spelling a composite with
`AlgebraicGeometry.SmallEtale.toEtaleSite` produces and which instance search does not unfold. -/
instance isContinuous_smallEtaleCompose_inclusion_map_obj_hom :
    @Functor.IsContinuous U.obj.left.obj.Etale _ (B.inclusion.obj (B.obj S hS)).Etale _
      (Etale.smallEtaleCompose (B.inclusion.map U.obj.hom))
      U.obj.left.obj.smallEtaleTopology S.smallEtaleTopology :=
  Etale.smallEtaleCompose_isContinuous _

/-- **Composition with `U ⟶ S` commutes with the embedding of the bounded site in Mathlib's.**
Both composites send `V ⟶ U` to the scheme `V` with structure morphism `V ⟶ U ⟶ S`. -/
def toEtaleSiteCompSmallEtaleComposeIso :
    toEtaleSite B U.obj.left.obj U.obj.left.property ⋙
        Etale.smallEtaleCompose (B.inclusion.map U.obj.hom) ≅
      smallEtalePostcompose B S hS U ⋙ toEtaleSite B S hS :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => by
    apply MorphismProperty.Over.Hom.ext
    exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- **Restriction along `U ⟶ S` corresponds under the dictionary.** Both composites are
precomposition with the two isomorphic composites of
`AlgebraicGeometry.SmallEtale.toEtaleSiteCompSmallEtaleComposeIso`, after forgetting the module
structure, which commutes with precomposition on the nose. -/
def etaleModulesIntEquivalenceRestrictionIso :
    (etaleModulesIntEquivalence B S hS).functor ⋙ abelianRestriction B S hS U ≅
      Stacks.EtaleCohomology.etaleModuleRestriction.{u, 0} ℤ (B.inclusion.map U.obj.hom) ⋙
        (etaleModulesIntEquivalence B U.obj.left.obj U.obj.left.property).functor :=
  haveI : (smallEtalePostcompose B S hS U ⋙ toEtaleSite B S hS).IsContinuous
      (SmallEtale.topology B U.obj.left.obj U.obj.left.property) S.smallEtaleTopology :=
    Functor.isContinuous_comp _ _ _ (SmallEtale.topology B S hS) _
  haveI : (toEtaleSite B U.obj.left.obj U.obj.left.property ⋙
      Etale.smallEtaleCompose (B.inclusion.map U.obj.hom)).IsContinuous
      (SmallEtale.topology B U.obj.left.obj U.obj.left.property) S.smallEtaleTopology :=
    Functor.isContinuous_comp _ _ _ U.obj.left.obj.smallEtaleTopology _
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (sheafCompose S.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}))
      (Functor.sheafPushforwardContinuousComp' (F := smallEtalePostcompose B S hS U)
          (G := toEtaleSite B S hS) (Iso.refl _) _ _ _ _ ≪≫
        Functor.sheafPushforwardContinuousIso
          (toEtaleSiteCompSmallEtaleComposeIso B S hS U).symm _ _ _ ≪≫
        (Functor.sheafPushforwardContinuousComp'
          (F := toEtaleSite B U.obj.left.obj U.obj.left.property)
          (G := Etale.smallEtaleCompose (B.inclusion.map U.obj.hom)) (Iso.refl _)
            _ _ _ _).symm) ≪≫
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Iso.refl _)
        ((toEtaleSite B U.obj.left.obj U.obj.left.property).sheafPushforwardContinuous
          AddCommGrpCat.{u + 1} (SmallEtale.topology B U.obj.left.obj U.obj.left.property)
          U.obj.left.obj.smallEtaleTopology) ≪≫
    Functor.associator _ _ _

/-- **Extension by zero corresponds under the dictionary.** Extension by zero is left adjoint to
restriction on both presentations, the dictionary is an equivalence, and restriction corresponds
under it (`AlgebraicGeometry.SmallEtale.etaleModulesIntEquivalenceRestrictionIso`); so the two
composites below are left adjoint to the same functor. -/
def etaleModulesIntEquivalenceExtensionByZeroIso :
    abelianExtensionByZero B S hS U ⋙ (etaleModulesIntEquivalence B S hS).inverse ≅
      (etaleModulesIntEquivalence B U.obj.left.obj U.obj.left.property).inverse ⋙
        Stacks.EtaleCohomology.etaleModuleExtensionByZero.{u, 0} ℤ (B.inclusion.map U.obj.hom) :=
  Adjunction.leftAdjointUniq
    (((abelianExtensionByZeroAdjunction B S hS U).comp
      (etaleModulesIntEquivalence B S hS).symm.toAdjunction).ofNatIsoRight
        (etaleModulesIntEquivalenceRestrictionIso B S hS U))
    ((etaleModulesIntEquivalence B U.obj.left.obj U.obj.left.property).symm.toAdjunction.comp
      (Stacks.EtaleCohomology.etaleModuleExtensionByZeroAdj.{u, 0} ℤ
        (B.inclusion.map U.obj.hom)))

end ExtensionByZero

end AlgebraicGeometry.SmallEtale

namespace Stacks.EtaleCohomology

/-! ### The comparison -/

section Comparison

/-- **A field is no larger than any nonempty scheme over it.** If `X` is a nonempty scheme over a
field `k` lying in the big étale site `B`, then `Spec k` lies in `B`: `k` embeds into a stalk of
`X`, whose cardinality is bounded by the size of `X`. -/
theorem contains_spec_field_of_nonempty (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (B : BigEtaleSite.{u}) (hX : B.Contains X) (x : X) :
    B.Contains (Spec (.of k)) := by
  have hinj : Function.Injective ((X.presheaf.germ ⊤ x trivial).hom.comp
      (f.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom)) := RingHom.injective _
  have h1 : Cardinal.mk k ≤ X.size :=
    (Cardinal.mk_le_of_injective hinj).trans (Scheme.mk_stalk_le_size X x)
  exact Scheme.size_Spec_lt_of_mk_le B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit
    (CommRingCat.of k) hX (h1.trans (Cardinal.self_le_power _ Cardinal.one_le_aleph0))

/-- Sections of a sheaf of modules over any object of the small étale site of an empty scheme
vanish. -/
private theorem isZero_obj_of_isEmpty (Λ : Type) [Ring Λ] (X : Scheme.{u}) [IsEmpty X]
    (F : EtaleModules.{u, 0} Λ X) (V : X.Etale) : IsZero (F.obj.obj (op V)) :=
  (F.isTerminalOfBotCover V (bot_mem_smallEtaleTopology_of_isEmpty V
    ⟨fun y => IsEmpty.false (α := X) (V.hom.base y)⟩)).isZero

/-- **A sheaf of modules on the small étale site of an empty scheme is zero**: every object of the
site is an empty scheme, covered by the empty family. -/
theorem isZero_etaleModules_of_isEmpty (Λ : Type) [Ring Λ] (X : Scheme.{u}) [IsEmpty X]
    (F : EtaleModules.{u, 0} Λ X) : IsZero F :=
  IsZero.of_full_of_faithful_of_isZero (sheafToPresheaf _ _) F
    ((Functor.isZero_iff _).2 fun V ↦ isZero_obj_of_isEmpty Λ X F V.unop)

attribute [local instance] HasDerivedCategory.standard

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]

omit [QuasiCompact f] [IsSeparated f] in
/-- The comparison of Tag 0GK1 over an empty scheme, where both groups vanish. -/
theorem nonempty_addEquiv_compactlySupportedCohomologyGroup_zero_of_isEmpty [IsEmpty X]
    (j : CompactificationOf (Over.mk f)) (B : BigEtaleSite.{u}) (hX : B.Contains X)
    (F : EtaleModules.{u, 0} ℤ X) :
    Nonempty ((compactlySupportedCohomologyGroup.{u, 0} k f j ℤ 0).obj
        ((DerivedCategory.Plus.singleFunctor (EtaleModules.{u, 0} ℤ X) 0).obj F) ≃+
      SmallEtale.compactlySupportedSections k X f B hX
        ((SmallEtale.etaleModulesIntEquivalence B X hX).functor.obj F)) := by
  obtain ⟨e1⟩ := nonempty_compactlySupportedCohomologyGroup_zero_iso k f j ℤ F
  have hL : IsZero ((etaleModuleGlobalSections.{u, 0} ℤ j.space).obj
      ((etaleModuleExtensionByZero.{u, 0} ℤ j.immersion).obj F)) :=
    Functor.map_isZero _ (Functor.map_isZero _ (isZero_etaleModules_of_isEmpty ℤ X F))
  have h1 : Subsingleton ((compactlySupportedCohomologyGroup.{u, 0} k f j ℤ 0).obj
      ((DerivedCategory.Plus.singleFunctor (EtaleModules.{u, 0} ℤ X) 0).obj F)) :=
    ModuleCat.isZero_iff_subsingleton.1 (hL.of_iso e1)
  have hsec := isZero_obj_of_isEmpty ℤ X F ((SmallEtale.toEtaleSite B X hX).obj
    (SmallEtale.final B X hX))
  have h2 : Subsingleton (((SmallEtale.etaleModulesIntEquivalence B X hX).functor.obj F).obj.obj
      (op (SmallEtale.final B X hX))) :=
    ModuleCat.isZero_iff_subsingleton.1 hsec
  exact ⟨{ toFun := fun _ => 0
           invFun := fun _ => 0
           left_inv := fun _ => Subsingleton.elim _ _
           right_inv := fun _ => Subsingleton.elim _ _
           map_add' := fun _ _ => Subsingleton.elim _ _ }⟩

/-- The comparison of Tag 0GK1 over a nonempty scheme, where the compactification lies in `B`
and Tag 0F75 applies. -/
theorem nonempty_addEquiv_compactlySupportedCohomologyGroup_zero_of_nonempty (x : X)
    (j : CompactificationOf (Over.mk f)) (B : BigEtaleSite.{u}) (hX : B.Contains X)
    (F : EtaleModules.{u, 0} ℤ X) :
    Nonempty ((compactlySupportedCohomologyGroup.{u, 0} k f j ℤ 0).obj
        ((DerivedCategory.Plus.singleFunctor (EtaleModules.{u, 0} ℤ X) 0).obj F) ≃+
      SmallEtale.compactlySupportedSections k X f B hX
        ((SmallEtale.etaleModulesIntEquivalence B X hX).functor.obj F)) := by
  obtain ⟨e1⟩ := nonempty_compactlySupportedCohomologyGroup_zero_iso k f j ℤ F
  have hk : B.Contains (Spec (.of k)) := contains_spec_field_of_nonempty k f B hX x
  have hXbar : B.Contains j.space :=
    Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact j.toBase hk
  let jB : B.obj X hX ⟶ B.obj j.space hXbar := ObjectProperty.homMk j.immersion
  let U : SmallEtale B j.space hXbar := ⟨Over.mk jB, inferInstanceAs (Etale j.immersion)⟩
  have : IsOpenImmersion (B.inclusion.map U.obj.hom) :=
    inferInstanceAs (IsOpenImmersion j.immersion)
  let DX := SmallEtale.etaleModulesIntEquivalence B X hX
  let DXb := SmallEtale.etaleModulesIntEquivalence B j.space hXbar
  let H := (abelianExtensionByZero B j.space hXbar U).obj (DX.functor.obj F)
  have e2 : (etaleModuleExtensionByZero.{u, 0} ℤ j.immersion).obj F ≅ DXb.inverse.obj H :=
    (etaleModuleExtensionByZero.{u, 0} ℤ j.immersion).mapIso (DX.unitIso.app F) ≪≫
      ((SmallEtale.etaleModulesIntEquivalenceExtensionByZeroIso B j.space hXbar U).app
        (DX.functor.obj F)).symm
  have hcomp : B.inclusion.map U.obj.hom ≫ j.toBase = f := Over.w j.obj.hom
  have hcss : ∀ (g : X ⟶ Spec (.of k)) [LocallyOfFiniteType g], g = f →
      SmallEtale.compactlySupportedSections k X g B hX (DX.functor.obj F) =
        SmallEtale.compactlySupportedSections k X f B hX (DX.functor.obj F) := by
    rintro g _ rfl
    rfl
  exact ⟨e1.toLinearEquiv.toAddEquiv.trans <|
    ((etaleModuleGlobalSections.{u, 0} ℤ j.space).mapIso e2).toLinearEquiv.toAddEquiv.trans <|
    (SmallEtale.etaleModuleGlobalSectionsAddEquiv B j.space hXbar (DXb.inverse.obj H)).trans <|
    (((sheafToPresheaf _ _).mapIso (DXb.counitIso.app H)).app
      (op (SmallEtale.final B j.space hXbar))).addCommGroupIsoToAddEquiv.trans <|
    AddSubgroup.topEquiv.symm.trans <|
    (AddEquiv.addSubgroupCongr (SmallEtale.compactlySupportedSections_eq_top_of_isProper k
      j.space j.toBase B hXbar H).symm).trans <|
    (SmallEtale.compactlySupportedSections_extensionByZero k B (B.obj j.space hXbar)
      j.toBase U (DX.functor.obj F)).symm.trans <|
    AddEquiv.addSubgroupCongr (hcss _ hcomp)⟩

/-- **Stacks Project, Tag 0GK1.** Let `X` be a separated scheme of finite type over a field `k`
and let `ℱ` be an abelian sheaf on `X_étale`, that is a sheaf of `ℤ`-modules. The group
`H⁰_c(X, ℱ)` of Definition 0GJZ, the zeroth cohomology of `RΓ_c(X, ℱ) = RΓ(Spec k, Rf_!ℱ)`
formed with a compactification `j : X ⟶ X̄`, agrees with the group `H⁰_c(X, ℱ)` of Definition
0F72 of sections of `ℱ` with support proper over `k`, the latter taken on the small étale site of
Tag 021B inside any big étale site `B` containing `X`, on which `ℱ` is read through
`AlgebraicGeometry.SmallEtale.etaleModulesIntEquivalence`.

Both groups are `H⁰(X̄, j_!ℱ)`: the first by
`Stacks.EtaleCohomology.nonempty_compactlySupportedCohomologyGroup_zero_iso`, the second by Tags
0F75 and 0F73. The source's torsion hypothesis is not used. -/
@[stacks 0GK1]
theorem nonempty_addEquiv_compactlySupportedCohomologyGroup_zero
    (j : CompactificationOf (Over.mk f)) (B : BigEtaleSite.{u}) (hX : B.Contains X)
    (F : EtaleModules.{u, 0} ℤ X) :
    Nonempty ((compactlySupportedCohomologyGroup.{u, 0} k f j ℤ 0).obj
        ((DerivedCategory.Plus.singleFunctor (EtaleModules.{u, 0} ℤ X) 0).obj F) ≃+
      SmallEtale.compactlySupportedSections k X f B hX
        ((SmallEtale.etaleModulesIntEquivalence B X hX).functor.obj F)) := by
  rcases isEmpty_or_nonempty X with _ | ⟨⟨x⟩⟩
  · exact nonempty_addEquiv_compactlySupportedCohomologyGroup_zero_of_isEmpty k f j B hX F
  · exact nonempty_addEquiv_compactlySupportedCohomologyGroup_zero_of_nonempty k f x j B hX F

end Comparison

end Stacks.EtaleCohomology

end
