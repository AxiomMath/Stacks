module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sheaves.Functors
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Cohomology.ColimitsHigherDirect.CohomologyOfOpen
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.CohomologyDirectSums
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.FilteredColimits.AbelianHigherDirectImage
public import StacksFrontier.Topology.Sheaves.Cohomology.FilteredColimits.CohomologyOverAQuasiCompactOpen
public import StacksFrontier.Topology.Sheaves.OpenImmersion.ModuleAdjunction
public import StacksFrontier.Topology.Sheaves.Sheaf.Abelian

/-!
# Higher direct images, filtered colimits and direct sums

For a quasi-compact and quasi-separated morphism of schemes, every higher direct image
functor on sheaves of abelian groups commutes with filtered colimits, and also with direct sums
indexed by an arbitrary type.

## Main results

* `Stacks.Cohomology.SchemeColimits.higherDirectImage_preservesFilteredColimits`: higher direct
  images along a quasi-compact and quasi-separated morphism preserve filtered colimits.
* `Stacks.Cohomology.SchemeColimits.higherDirectImage_preservesColimitsOfShape_discrete`: the
  same functors preserve direct sums indexed by an arbitrary type.

## Implementation notes

The higher direct image `R^p f_*` is represented by the `p`-th right derived functor of
`TopCat.Sheaf.pushforward AddCommGrpCat f.base`. Preservation is stated functorially, so the
result includes the canonical comparison isomorphism and its naturality in every filtered
diagram. No enough-injectives hypothesis is needed: abelian sheaves on a space are a
Grothendieck abelian category, so the instance Mathlib's right derived functor asks for is
found by instance search.

The source reduces to Stacks 01FF, which is a statement about sheaves of *modules* on a ringed
space. The bridge is the constant sheaf of rings `ℤ`: an abelian sheaf on `X` is the same thing
as a sheaf of modules over it, by `abelianSheafToIntegerModule`, whose composite with the
forgetful functor to abelian sheaves is the identity up to natural isomorphism
(`abelianSheafToIntegerModule_underlyingIso`). Cohomology computed in sheaves of modules and
cohomology of the underlying abelian sheaf agree by Stacks 03FD
(`ModuleSheafCohomology.moduleSheafCohomologyIsoUnderlying`), and cohomology over an open agrees
with cohomology of the restriction to that open subspace by Stacks 01E1
(`AlgebraicGeometry.cohomologyOverNatIsoRestriction`), so Stacks 01FF applies on the open
subscheme `f⁻¹(V)` for `V` an affine open of `S`.

A direct sum is not a filtered colimit, so the direct-sum statement is not a consequence of the
filtered one; what differs between the two proofs is only their local input. Over the inverse
image of an affine open the filtered case appeals to Stacks 01FF
(`Stacks.Cohomology.Vanishing.isIso_colimit_post_Hfunctor_of_isCompact`) and the direct-sum case
to its direct-sum companion
`Stacks.Cohomology.DirectSum.preservesColimitsOfShape_discrete_Hfunctor`, which adds additivity
of `H^q(U, -)` to that lemma. Everything between — the passage from abelian sheaves to
`ULift ℤ`-modules, the restriction to an open subspace, and Stacks 0H7A — holds for a diagram of
arbitrary shape, so the three steps are proved here for an arbitrary small shape and the filtered
statements are read off from them.

## References

* [Stacks Project, Tag 07TB](https://stacks.math.columbia.edu/tag/07TB)
* [Stacks Project, Tag 01FF](https://stacks.math.columbia.edu/tag/01FF)
* [Stacks Project, Tag 0H7A](https://stacks.math.columbia.edu/tag/0H7A)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace Stacks.Cohomology.SchemeColimits

/-- The quasi-compact opens of a quasi-separated scheme form a basis: the affine opens do, and
they are quasi-compact. -/
private theorem hasBasisOfCompactOpens_of_quasiSeparatedScheme (T : AlgebraicGeometry.Scheme.{u})
    [QuasiSeparatedSpace T.carrier] : PrespectralSpace T.carrier := by
  refine PrespectralSpace.of_isTopologicalBasis (B := (↑) '' T.affineOpens) ?_ ?_
  · exact T.isBasis_affineOpens
  · rintro _ ⟨U, hU, rfl⟩
    exact hU.isCompact

/-- The constant presheaf of rings `ℤ` on a space. -/
@[sga "3 I 3.1.3" "special case"]
private abbrev integerPresheaf (X : TopCat.{u}) : (Opens X)ᵒᵖ ⥤ RingCat.{u} :=
  (Functor.const (Opens X)ᵒᵖ).obj (RingCat.of (ULift.{u, 0} ℤ))

/-- The ring isomorphism `ULift ℤ →+* ℤ` used to view an abelian group as a `ULift ℤ`-module. -/
private def integerScalarMap : ULift.{u, 0} ℤ →+* ℤ where
  toFun := ULift.down
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- A presheaf of abelian groups as a presheaf of modules over the constant presheaf `ULift ℤ`. -/
private noncomputable def integerModulePresheaf (X : TopCat.{u})
    (F : X.Presheaf AddCommGrpCat.{u}) : PresheafOfModules (integerPresheaf X) := by
  refine @PresheafOfModules.ofPresheaf _ _ (integerPresheaf X) F ?_ ?_
  · intro U
    exact Module.compHom (F.obj U) integerScalarMap
  · intro A B f r m
    change (F.map f).hom (integerScalarMap r • m) = integerScalarMap r • (F.map f).hom m
    exact map_zsmul (F.map f).hom (integerScalarMap r) m

/-- `integerModulePresheaf` as a functor on presheaves of abelian groups. -/
private noncomputable def integerModulePresheafFunctor (X : TopCat.{u}) :
    X.Presheaf AddCommGrpCat.{u} ⥤ PresheafOfModules.{u} (integerPresheaf X) where
  obj := integerModulePresheaf X
  map {F G} φ := {
    app := fun U => by
      letI : Module ((integerPresheaf X).obj U) (F.obj U) :=
        Module.compHom (F.obj U) integerScalarMap
      letI : Module ((integerPresheaf X).obj U) (G.obj U) :=
        Module.compHom (G.obj U) integerScalarMap
      exact ModuleCat.ofHom {
        toFun := φ.app U
        map_add' := by simp
        map_smul' := by
          intro r m
          change φ.app U (integerScalarMap r • m) = integerScalarMap r • φ.app U m
          exact map_zsmul (φ.app U).hom (integerScalarMap r) m }
    naturality := by
      intro U V f
      ext m
      exact congrArg (fun g => g m) (φ.naturality f) }
  map_id F := by ext U m; rfl
  map_comp φ ψ := by ext U m; rfl

/-- The constant sheaf of rings `ULift ℤ` on a space: the structure sheaf used to see abelian
sheaves as sheaves of modules. -/
@[sga "4 IV 11.1.5" "special case"]
private noncomputable def integerRingSheaf (X : TopCat.{u}) :
    Sheaf (Opens.grothendieckTopology X) RingCat.{u} :=
  (constantSheaf (Opens.grothendieckTopology X) RingCat.{u}).obj
    (RingCat.of (ULift.{u, 0} ℤ))

/-- The space `X` with `integerRingSheaf X` as its structure sheaf. -/
private noncomputable def integerSheafedSpace (X : TopCat.{u}) :
    AlgebraicGeometry.SheafedSpace RingCat.{u} :=
  { carrier := X
    presheaf := (integerRingSheaf X).obj
    IsSheaf := (integerRingSheaf X).property }

/-- The sheafification map from the constant presheaf to the constant sheaf of rings `ULift ℤ`. -/
private noncomputable def integerSheafificationMap (X : TopCat.{u}) :
    integerPresheaf X ⟶ (integerRingSheaf X).obj := by
  change integerPresheaf X ⟶
    (sheafToPresheaf (Opens.grothendieckTopology X) RingCat).obj
      ((presheafToSheaf (Opens.grothendieckTopology X) RingCat).obj
        (integerPresheaf X))
  exact toSheafify (Opens.grothendieckTopology X) (integerPresheaf X)

private instance integerSheafificationMap_locallyInjective (X : TopCat.{u}) :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      (integerSheafificationMap X) := by
  change Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
    (toSheafify (Opens.grothendieckTopology X) (integerPresheaf X))
  infer_instance

private instance integerSheafificationMap_locallySurjective (X : TopCat.{u}) :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      (integerSheafificationMap X) := by
  change Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
    (toSheafify (Opens.grothendieckTopology X) (integerPresheaf X))
  infer_instance

/-- An abelian sheaf on `X` as a sheaf of modules over the constant sheaf of rings `ULift ℤ`. -/
private noncomputable def abelianSheafToIntegerModule (X : TopCat.{u}) :
    X.Sheaf AddCommGrpCat.{u} ⥤ SheafOfModules.{u} (integerRingSheaf X) := by
  let J := Opens.grothendieckTopology X
  letI : Presheaf.IsLocallyInjective J (integerSheafificationMap X) :=
    integerSheafificationMap_locallyInjective X
  letI : Presheaf.IsLocallySurjective J (integerSheafificationMap X) :=
    integerSheafificationMap_locallySurjective X
  exact sheafToPresheaf J AddCommGrpCat.{u} ⋙ integerModulePresheafFunctor X ⋙
    PresheafOfModules.sheafification
      (J := J) (R := integerRingSheaf X) (integerSheafificationMap X)

/-- Forgetting the `ULift ℤ`-module structure recovers the abelian sheaf: the composite of
`abelianSheafToIntegerModule` with `SheafOfModules.toSheaf` is the identity. -/
private noncomputable def abelianSheafToIntegerModule_underlyingIso
    (X : TopCat.{u}) :
    abelianSheafToIntegerModule X ⋙
        SheafOfModules.toSheaf (integerRingSheaf X) ≅
      𝟭 (X.Sheaf AddCommGrpCat.{u}) := by
  let J := Opens.grothendieckTopology X
  letI : Presheaf.IsLocallyInjective J (integerSheafificationMap X) :=
    integerSheafificationMap_locallyInjective X
  letI : Presheaf.IsLocallySurjective J (integerSheafificationMap X) :=
    integerSheafificationMap_locallySurjective X
  change sheafToPresheaf J AddCommGrpCat ⋙ presheafToSheaf J AddCommGrpCat ≅ _
  refine NatIso.ofComponents
    (fun F => asIso ((sheafificationAdjunction J AddCommGrpCat).counit.app F)) ?_
  intro F G φ
  exact (sheafificationAdjunction J AddCommGrpCat).counit.naturality φ

/-- The forgetful functor from sheaves of modules to abelian sheaves preserves colimits of every
small shape: it is reflective and the sheafification it is right adjoint to preserves them. -/
private theorem moduleToSheaf_preservesColimitsOfShape (X : TopCat.{u})
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (I : Type u) [SmallCategory I] :
    PreservesColimitsOfShape I (SheafOfModules.toSheaf.{u,u,u,u} R) := by
  refine ⟨fun {D} => ⟨fun {c} hc => ?_⟩⟩
  let L := PresheafOfModules.sheafification.{u,u,u,u} (𝟙 R.obj)
  let adj : L ⊣ _ := PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)
  let G := SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)
  have hL : PreservesColimitsOfShape I L :=
    adj.leftAdjoint_preservesColimits.preservesColimitsOfShape
  have hP : PreservesColimitsOfShape I
      (PresheafOfModules.toPresheaf.{u,u,u,u} R.obj) := inferInstance
  have hS : PreservesColimitsOfShape I
      (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
    (sheafificationAdjunction (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}).leftAdjoint_preservesColimits.preservesColimitsOfShape
  have hLT : PreservesColimitsOfShape I
      (L ⋙ SheafOfModules.toSheaf.{u,u,u,u} R) :=
    preservesColimitsOfShape_of_natIso
      (PresheafOfModules.sheafificationCompToSheaf (𝟙 R.obj)).symm
  have e : (D ⋙ G) ⋙ L ≅ D :=
    NatIso.ofComponents (fun j => (asIso adj.counit).app (D.obj j)) (by
      intro i j f
      exact (asIso adj.counit).hom.naturality (D.map f))
  have h1 : PreservesColimit (D ⋙ G) L := hL.preservesColimit
  have h2 : PreservesColimit (D ⋙ G)
      (L ⋙ SheafOfModules.toSheaf.{u,u,u,u} R) :=
    hLT.preservesColimit
  have hpc : PreservesColimit ((D ⋙ G) ⋙ L)
      (SheafOfModules.toSheaf.{u,u,u,u} R) :=
    preservesColimit_of_preserves_colimit_cocone
      (isColimitOfPreserves L (colimit.isColimit (D ⋙ G)))
      (isColimitOfPreserves (L ⋙ SheafOfModules.toSheaf.{u,u,u,u} R)
        (colimit.isColimit (D ⋙ G)))
  exact (preservesColimit_of_iso_diagram
    (SheafOfModules.toSheaf.{u,u,u,u} R) e).preserves hc

/-- The forgetful functor from sheaves of modules to abelian sheaves preserves filtered
colimits: it is reflective and the sheafification it is right adjoint to preserves them. -/
private theorem moduleToSheaf_preservesFilteredColimits (X : TopCat.{u})
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) :
    PreservesFilteredColimits (SheafOfModules.toSheaf.{u,u,u,u} R) :=
  ⟨fun I _ _ => moduleToSheaf_preservesColimitsOfShape X R I⟩

/-- `abelianSheafToIntegerModule` preserves colimits of every small shape. -/
private theorem abelianSheafToIntegerModule_preservesColimitsOfShape (X : TopCat.{u})
    (I : Type u) [SmallCategory I] :
    PreservesColimitsOfShape I (abelianSheafToIntegerModule X) := by
  have hU : PreservesColimitsOfShape I
      (SheafOfModules.toSheaf.{u,u,u,u} (integerRingSheaf X)) :=
    moduleToSheaf_preservesColimitsOfShape X (integerRingSheaf X) I
  have hLU : PreservesColimitsOfShape I
      (abelianSheafToIntegerModule X ⋙
        SheafOfModules.toSheaf.{u,u,u,u} (integerRingSheaf X)) := by
    refine ⟨fun {D} => ⟨fun {c} hc => ?_⟩⟩
    have hId : PreservesColimit D (𝟭 (TopCat.Sheaf AddCommGrpCat.{u} X)) :=
      ⟨fun {c} hc => ⟨hc⟩⟩
    exact (preservesColimit_of_natIso D
      (abelianSheafToIntegerModule_underlyingIso X).symm).preserves hc
  have : ReflectsColimitsOfShape I
      (SheafOfModules.toSheaf.{u,u,u,u} (integerRingSheaf X)) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms (J := I)
  exact preservesColimitsOfShape_of_reflects_of_preserves
    (abelianSheafToIntegerModule X)
    (SheafOfModules.toSheaf.{u,u,u,u} (integerRingSheaf X))

/-- `abelianSheafToIntegerModule` preserves filtered colimits. -/
private theorem abelianSheafToIntegerModule_preservesFilteredColimits (X : TopCat.{u}) :
    PreservesFilteredColimits (abelianSheafToIntegerModule X) :=
  ⟨fun I _ _ => abelianSheafToIntegerModule_preservesColimitsOfShape X I⟩

/-- Restriction of sheaves of modules to an open subspace preserves colimits of every small
shape: on underlying abelian sheaves it is the inverse image functor, which is a left
adjoint. -/
private theorem restMod_preservesColimitsOfShape
    (X : TopCat.{u}) (U : Opens X) (I : Type u) [SmallCategory I] :
    PreservesColimitsOfShape I (restMod (integerSheafedSpace X) U) := by
  let T := integerSheafedSpace X
  let X' := (Opens.toTopCat X).obj U
  let j := Opens.inclusion' U
  let R := integerRingSheaf X
  let R' := OUSh T U
  let pull := TopCat.Sheaf.pullback AddCommGrpCat.{u} j
  let adj := TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} j
  have hUnderlyingNaive :
      restMod T U ⋙ SheafOfModules.toSheaf R' ≅
        SheafOfModules.toSheaf R ⋙ U.isOpenEmbedding.sheafPullback AddCommGrpCat.{u} := by
    refine NatIso.ofComponents (fun M => ?_) ?_
    · exact Iso.refl _
    · intro M N φ
      rfl
  have hUnderlying :
      restMod T U ⋙ SheafOfModules.toSheaf R' ≅
        SheafOfModules.toSheaf R ⋙ pull :=
    hUnderlyingNaive.trans
      (Functor.isoWhiskerLeft (SheafOfModules.toSheaf R)
        (U.isOpenEmbedding.sheafPullbackIso AddCommGrpCat.{u}).symm)
  have hSource : PreservesColimitsOfShape I (SheafOfModules.toSheaf R) :=
    moduleToSheaf_preservesColimitsOfShape X R I
  have hTarget : PreservesColimitsOfShape I (SheafOfModules.toSheaf R') :=
    moduleToSheaf_preservesColimitsOfShape X' R' I
  have hPull : PreservesColimitsOfShape I pull :=
    adj.leftAdjoint_preservesColimits.preservesColimitsOfShape
  have hComp : PreservesColimitsOfShape I (SheafOfModules.toSheaf R ⋙ pull) := by
    refine ⟨fun {D} => ⟨fun {c} hc => ?_⟩⟩
    have h1 : IsColimit ((SheafOfModules.toSheaf R).mapCocone c) :=
      (hSource.preservesColimit.preserves hc).some
    exact ⟨(hPull.preservesColimit.preserves h1).some⟩
  have hRestComp : PreservesColimitsOfShape I
      (restMod T U ⋙ SheafOfModules.toSheaf R') :=
    (preservesColimitsOfShape_iff_of_natIso hUnderlying).mpr hComp
  have : ReflectsColimitsOfShape I (SheafOfModules.toSheaf R') :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms (J := I)
  exact preservesColimitsOfShape_of_reflects_of_preserves
    (restMod T U) (SheafOfModules.toSheaf R')

/-- Restriction of sheaves of modules to an open subspace preserves filtered colimits: on
underlying abelian sheaves it is the inverse image functor, which is a left adjoint. -/
private theorem restMod_preservesFilteredColimits
    (X : TopCat.{u}) (U : Opens X) :
    PreservesFilteredColimits (restMod (integerSheafedSpace X) U) :=
  ⟨fun I _ _ => restMod_preservesColimitsOfShape X U I⟩

/-- **Cohomology of an abelian sheaf over an open, as cohomology of modules on the open
subspace.** Composing Stacks 03FD (cohomology of a sheaf of modules agrees with cohomology of
its underlying abelian sheaf) with Stacks 01E1 (cohomology over an open agrees with cohomology
of the restriction) identifies `H^p(U, -)` on abelian sheaves with the cohomology of the
restricted `ULift ℤ`-module on the open subspace. -/
private theorem nonempty_integerCohomologyToRestrictedModulesIso
    (X : TopCat.{u}) (U : Opens X) (p : ℕ)
    [EnoughInjectives (SheafOfModules
      (OUSh (integerSheafedSpace X) U))] :
    Nonempty (Stacks.Cohomology.AbelianSheaf.cohomologyOver.{u, u} U p ≅
      abelianSheafToIntegerModule X ⋙
        restMod (integerSheafedSpace X) U ⋙
          Hfunctor (OUSh (integerSheafedSpace X) U) ⊤ p) := by
  classical
  obtain ⟨-, -, hOpens⟩ := ModuleSheafCohomology.moduleSheafCohomologyIsoUnderlying
    (J := Opens.grothendieckTopology X) (integerRingSheaf X)
  obtain ⟨eSite, -⟩ := hOpens U
  have eSite' :
    Hfunctor (integerRingSheaf X) U p ≅
        SheafOfModules.toSheaf (integerRingSheaf X) ⋙
          Stacks.Cohomology.AbelianSheaf.cohomologyOver.{u, u} U p := by
    change Hfunctor (integerRingSheaf X) U p ≅
      SheafOfModules.toSheaf (integerRingSheaf X) ⋙
        ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat).obj (op U)).rightDerived p
    exact eSite p
  have eOpen :
      Hfunctor (integerRingSheaf X) U p ≅
        restMod (integerSheafedSpace X) U ⋙
          Hfunctor (OUSh (integerSheafedSpace X) U) ⊤ p :=
    AlgebraicGeometry.cohomologyOverNatIsoRestriction
      (X := integerSheafedSpace X) (U := U) (p := p)
  have eLift := abelianSheafToIntegerModule_underlyingIso X
  exact ⟨calc
    Stacks.Cohomology.AbelianSheaf.cohomologyOver.{u, u} U p ≅
        𝟭 (X.Sheaf AddCommGrpCat.{u}) ⋙
          Stacks.Cohomology.AbelianSheaf.cohomologyOver.{u, u} U p :=
      (Functor.leftUnitor _).symm
    _ ≅ (abelianSheafToIntegerModule X ⋙
        SheafOfModules.toSheaf (integerRingSheaf X)) ⋙
          Stacks.Cohomology.AbelianSheaf.cohomologyOver.{u, u} U p :=
      Functor.isoWhiskerRight eLift.symm _
    _ ≅ abelianSheafToIntegerModule X ⋙
        (SheafOfModules.toSheaf (integerRingSheaf X) ⋙
          Stacks.Cohomology.AbelianSheaf.cohomologyOver.{u, u} U p) :=
      Functor.associator _ _ _
    _ ≅ abelianSheafToIntegerModule X ⋙ Hfunctor (integerRingSheaf X) U p :=
      Functor.isoWhiskerLeft _ eSite'.symm
    _ ≅ abelianSheafToIntegerModule X ⋙
        (restMod (integerSheafedSpace X) U ⋙
          Hfunctor (OUSh (integerSheafedSpace X) U) ⊤ p) :=
      Functor.isoWhiskerLeft _ eOpen
    _ ≅ abelianSheafToIntegerModule X ⋙
        restMod (integerSheafedSpace X) U ⋙
          Hfunctor (OUSh (integerSheafedSpace X) U) ⊤ p :=
      (Functor.associator _ _ _).symm⟩

/-- The pushforward of abelian sheaves along a morphism of schemes is additive. -/
noncomputable instance pushforwardAbelianSheaf_additive
    {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- For a quasi-compact and quasi-separated morphism of schemes, its `p`-th higher direct
image functor on sheaves of abelian groups preserves all filtered colimits. -/
@[stacks 07TB]
instance higherDirectImage_preservesFilteredColimits
    {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
    [AlgebraicGeometry.QuasiCompact f] [AlgebraicGeometry.QuasiSeparated f] (p : ℕ) :
    PreservesFilteredColimits
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base).rightDerived p) := by
  refine ⟨fun I _ _ => ?_⟩
  refine ⟨?_⟩
  intro F
  have hBasis : TopologicalSpace.Opens.IsBasis {V : TopologicalSpace.Opens S.carrier |
      PreservesColimit F (Stacks.Cohomology.AbelianSheaf.cohomologyOver.{u, u}
        ((TopologicalSpace.Opens.map f.base).obj V) p)} := by
    change IsTopologicalBasis (((↑) : Opens S.carrier → Set S.carrier) ''
      {V : Opens S.carrier |
      PreservesColimit F (Stacks.Cohomology.AbelianSheaf.cohomologyOver.{u, u}
        ((TopologicalSpace.Opens.map f.base).obj V) p)})
    apply S.isBasis_affineOpens.isTopologicalBasis_of_exists_subset
    · intro U hU
      rcases hU with ⟨V₀, hV₀, rfl⟩
      exact V₀.isOpen
    · intro U hU x hx
      rcases hU with ⟨V₀, hV₀, rfl⟩
      have hPres : PreservesColimit F
        (Stacks.Cohomology.AbelianSheaf.cohomologyOver.{u, u}
          ((TopologicalSpace.Opens.map f.base).obj V₀) p) := by
        let W : X.Opens := (TopologicalSpace.Opens.map f.base).obj V₀
        have hWcompact : IsCompact (W : Set X.carrier) := by
          simpa [W] using f.isCompact_preimage hV₀.isCompact
        let Vscheme : AlgebraicGeometry.Scheme :=
          AlgebraicGeometry.Scheme.Opens.toScheme (X := S) V₀
        let T : AlgebraicGeometry.Scheme :=
          AlgebraicGeometry.Scheme.Opens.toScheme (X := X) W
        have hVqs : QuasiSeparatedSpace Vscheme :=
          (isQuasiSeparated_iff_quasiSeparatedSpace _ V₀.isOpen).1 hV₀.isQuasiSeparated
        let : QuasiSeparatedSpace Vscheme := hVqs
        have hWqs : QuasiSeparatedSpace T :=
          AlgebraicGeometry.quasiSeparatedSpace_of_quasiSeparated
            (f.resLE V₀ W le_rfl)
        let : QuasiSeparatedSpace T := hWqs
        have hCompactBasis : PrespectralSpace T.carrier :=
          hasBasisOfCompactOpens_of_quasiSeparatedScheme T
        have hCompactIntersections : QuasiSeparatedSpace T.carrier := hWqs
        let R := OUSh (integerSheafedSpace X) W
        let Y : TopCat :=
          (Opens.toTopCat (integerSheafedSpace X).carrier).obj W
        let G := abelianSheafToIntegerModule X ⋙
          restMod (integerSheafedSpace X) W
        let D := F ⋙ G
        let : EnoughInjectives (SheafOfModules R) := by
          let : IsGrothendieckAbelian (SheafOfModules R) := inferInstance
          exact IsGrothendieckAbelian.enoughInjectives
        let : CompactSpace Y := isCompact_iff_compactSpace.mp hWcompact
        have hModule : IsIso (colimit.post D (Hfunctor R ⊤ p)) :=
          Stacks.Cohomology.Vanishing.isIso_colimit_post_Hfunctor_of_isCompact
            R hCompactBasis hCompactIntersections D ⊤ isCompact_univ p
        have hG : PreservesColimitsOfShape I G := by
          have hA : PreservesColimitsOfShape I (abelianSheafToIntegerModule X) :=
            (abelianSheafToIntegerModule_preservesFilteredColimits X).preserves_filtered_colimits I
          have hB : PreservesColimitsOfShape I
              (restMod (integerSheafedSpace X) W) :=
            (restMod_preservesFilteredColimits X W).preserves_filtered_colimits I
          refine ⟨?_⟩
          intro D
          refine ⟨?_⟩
          intro c hc
          have h1 : IsColimit
              ((abelianSheafToIntegerModule X).mapCocone c) :=
            (hA.preservesColimit.preserves hc).some
          exact ⟨(hB.preservesColimit.preserves h1).some⟩
        have hGPost : IsIso (colimit.post F G) := by
          let : PreservesColimit F G := hG.preservesColimit
          infer_instance
        have hPostComposition : IsIso (colimit.post F (G ⋙ Hfunctor R ⊤ p)) := by
          rw [← colimit.post_post F G (Hfunctor R ⊤ p)]
          let : IsIso (colimit.post D (Hfunctor R ⊤ p)) := hModule
          let : IsIso (colimit.post F G) := hGPost
          infer_instance
        let : IsIso (colimit.post F (G ⋙ Hfunctor R ⊤ p)) := hPostComposition
        have hModulePres : PreservesColimit F (G ⋙ Hfunctor R ⊤ p) :=
          preservesColimit_of_isIso_post (F := F) (G := G ⋙ Hfunctor R ⊤ p)
        let := hModulePres
        obtain ⟨hCohomologyIso⟩ := nonempty_integerCohomologyToRestrictedModulesIso X W p
        exact (preservesColimit_iff_of_natIso F hCohomologyIso.symm).mp hModulePres
      exact ⟨V₀, ⟨V₀, hPres, rfl⟩, hx, fun _ hx => hx⟩
  exact Stacks.Cohomology.AbelianSheaf.preservesColimit_higherDirectImage_of_isBasis
    (f := f.base) F p hBasis

/-- **For a quasi-compact and quasi-separated morphism of schemes, its `p`-th higher direct
image functor on sheaves of abelian groups preserves direct sums indexed by an arbitrary
type.**

A direct sum is not a filtered colimit, so this does not follow from
`Stacks.Cohomology.SchemeColimits.higherDirectImage_preservesFilteredColimits`. The proof is the
same reduction along Stacks 0H7A to the inverse images of the affine opens of the target, with
Stacks 01FF replaced over each of them by its direct-sum companion
`Stacks.Cohomology.DirectSum.preservesColimitsOfShape_discrete_Hfunctor`.

Stacks 07TB is the filtered-colimit statement, carried by
`Stacks.Cohomology.SchemeColimits.higherDirectImage_preservesFilteredColimits`. The
direct-sum form below is its companion, which proofs citing 07TB for arbitrary direct sums
need, and it carries no tag of its own. -/
instance higherDirectImage_preservesColimitsOfShape_discrete
    {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
    [AlgebraicGeometry.QuasiCompact f] [AlgebraicGeometry.QuasiSeparated f] (p : ℕ)
    (α : Type u) :
    PreservesColimitsOfShape (Discrete α)
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base).rightDerived p) := by
  refine ⟨?_⟩
  intro F
  have hBasis : TopologicalSpace.Opens.IsBasis {V : TopologicalSpace.Opens S.carrier |
      PreservesColimit F (Stacks.Cohomology.AbelianSheaf.cohomologyOver.{u, u}
        ((TopologicalSpace.Opens.map f.base).obj V) p)} := by
    change IsTopologicalBasis (((↑) : Opens S.carrier → Set S.carrier) ''
      {V : Opens S.carrier |
      PreservesColimit F (Stacks.Cohomology.AbelianSheaf.cohomologyOver.{u, u}
        ((TopologicalSpace.Opens.map f.base).obj V) p)})
    apply S.isBasis_affineOpens.isTopologicalBasis_of_exists_subset
    · intro U hU
      rcases hU with ⟨V₀, hV₀, rfl⟩
      exact V₀.isOpen
    · intro U hU x hx
      rcases hU with ⟨V₀, hV₀, rfl⟩
      have hPres : PreservesColimit F
        (Stacks.Cohomology.AbelianSheaf.cohomologyOver.{u, u}
          ((TopologicalSpace.Opens.map f.base).obj V₀) p) := by
        let W : X.Opens := (TopologicalSpace.Opens.map f.base).obj V₀
        have hWcompact : IsCompact (W : Set X.carrier) := by
          simpa [W] using f.isCompact_preimage hV₀.isCompact
        let T : AlgebraicGeometry.Scheme :=
          AlgebraicGeometry.Scheme.Opens.toScheme (X := X) W
        have hVqs : QuasiSeparatedSpace
            (AlgebraicGeometry.Scheme.Opens.toScheme (X := S) V₀) :=
          (isQuasiSeparated_iff_quasiSeparatedSpace _ V₀.isOpen).1 hV₀.isQuasiSeparated
        let : QuasiSeparatedSpace
            (AlgebraicGeometry.Scheme.Opens.toScheme (X := S) V₀) := hVqs
        have hWqs : QuasiSeparatedSpace T :=
          AlgebraicGeometry.quasiSeparatedSpace_of_quasiSeparated
            (f.resLE V₀ W le_rfl)
        let : QuasiSeparatedSpace T := hWqs
        have hCompactBasis : PrespectralSpace T.carrier :=
          hasBasisOfCompactOpens_of_quasiSeparatedScheme T
        have hCompactIntersections : QuasiSeparatedSpace T.carrier := hWqs
        let R := OUSh (integerSheafedSpace X) W
        let Y : TopCat :=
          (Opens.toTopCat (integerSheafedSpace X).carrier).obj W
        let G := abelianSheafToIntegerModule X ⋙
          restMod (integerSheafedSpace X) W
        let : EnoughInjectives (SheafOfModules R) := by
          let : IsGrothendieckAbelian (SheafOfModules R) := inferInstance
          exact IsGrothendieckAbelian.enoughInjectives
        let : CompactSpace Y := isCompact_iff_compactSpace.mp hWcompact
        have hModule : PreservesColimitsOfShape (Discrete α) (Hfunctor R ⊤ p) :=
          Stacks.Cohomology.DirectSum.preservesColimitsOfShape_discrete_Hfunctor
            R hCompactBasis hCompactIntersections ⊤ isCompact_univ p α
        have hG : PreservesColimitsOfShape (Discrete α) G := by
          have hA : PreservesColimitsOfShape (Discrete α)
              (abelianSheafToIntegerModule X) :=
            abelianSheafToIntegerModule_preservesColimitsOfShape X (Discrete α)
          have hB : PreservesColimitsOfShape (Discrete α)
              (restMod (integerSheafedSpace X) W) :=
            restMod_preservesColimitsOfShape X W (Discrete α)
          refine ⟨?_⟩
          intro D
          refine ⟨?_⟩
          intro c hc
          have h1 : IsColimit
              ((abelianSheafToIntegerModule X).mapCocone c) :=
            (hA.preservesColimit.preserves hc).some
          exact ⟨(hB.preservesColimit.preserves h1).some⟩
        have hModulePres : PreservesColimit F (G ⋙ Hfunctor R ⊤ p) := by
          refine ⟨?_⟩
          intro c hc
          have h1 : IsColimit (G.mapCocone c) :=
            (hG.preservesColimit.preserves hc).some
          exact ⟨(hModule.preservesColimit.preserves h1).some⟩
        obtain ⟨hCohomologyIso⟩ := nonempty_integerCohomologyToRestrictedModulesIso X W p
        exact (preservesColimit_iff_of_natIso F hCohomologyIso.symm).mp hModulePres
      exact ⟨V₀, ⟨V₀, hPres, rfl⟩, hx, fun _ hx => hx⟩
  exact Stacks.Cohomology.AbelianSheaf.preservesColimit_higherDirectImage_of_isBasis
    (f := f.base) F p hBasis

end Stacks.Cohomology.SchemeColimits

end
