module

public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatShortExactSequence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkLinearEquiv
public import StacksFrontier.AlgebraicGeometry.Chow.CalculationMultiplicities.TwoPeriodic
public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.Multiplicity
public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.Support
public import StacksFrontier.AlgebraicGeometry.Chow.DeterminantsFiniteLength.RestrictScalars
public import StacksFrontier.AlgebraicGeometry.Chow.DimensionFunction.PrincipalDivisorFamily
public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexesDeterminants.Comparison
public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexesHerbrand.Length
public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicLengthDeterminantFormula
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalenceDefs
public import StacksFrontier.AlgebraicGeometry.Chow.RationalFunctions.FunctionField
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeDimension
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Support
public import StacksFrontier.AlgebraicGeometry.FiberRank.GenericPoint
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.KernelCokernel
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.AffineOpen
public import StacksFrontier.AlgebraicGeometry.Properties.PrincipalOpens.Sections
public import StacksFrontier.Topology.Sheaves.Functors.Module.SemilinearStalk
public import StacksFrontier.Topology.Sheaves.Modules.Colimits
import StacksFrontier.AlgebraicGeometry.Chow.DivisorTransport.Order
public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexHomologyCycles.DeterminantsAndComponents
import all StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexHomologyCycles.DeterminantsAndComponents

/-!
# Two-periodic complexes on a coherent sheaf: the complex of stalks

Let `X` be a scheme locally of finite type over the base of chapter 42 of the Stacks Project and
let `(F, φ, ψ)` be a `(2, 1)`-periodic complex of a coherent `𝒪_X`-module, presented as a
`ZMod 2`-indexed cochain complex `K` of `𝒪_X`-modules with isomorphisms `K.X i ≅ F`.

The cohomology sheaves of `K` are coherent. The stalk functor at a point `x`, valued in modules
over the local ring `𝒪_{X,x}`, is exact, so the stalk of the cohomology of `K` is the cohomology of
the complex of stalks; hence the multiplicities of the two cohomology sheaves at `x` are the
lengths of the cohomology of the complex of stalks, and their difference is its periodic length.
Conjugating the differentials by the chosen isomorphisms presents the complex of stalks as a pair
of endomorphisms of the stalk `F_x` over `𝒪_{X,x}`, exact in both orders as soon as the cohomology
stalks vanish.

## References

* [Stacks Project, Tag 02QW](https://stacks.math.columbia.edu/tag/02QW)
* [Stacks Project, Tag 02SB](https://stacks.math.columbia.edu/tag/02SB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.SheafOfModules.FlatShortExact TopologicalSpace

universe u

namespace Stacks.Chow

/-- On a locally Noetherian scheme a coherent module is of finite presentation. -/
private theorem finitePresentation_of_coherent {X : Scheme.{u}}
    [IsLocallyNoetherian X] (F : X.Modules) [F.IsCoherent] :
    F.IsFinitePresentation := by
  have hq : F.IsQuasicoherent ∧ F.IsFiniteType :=
    ((Stacks.AlgebraicGeometry.CoherenceCriteria.coherent_tfae X F).out 2 1).symm.mp
      (show F.IsCoherent from inferInstance)
  exact ((Stacks.AlgebraicGeometry.CoherenceCriteria.coherent_tfae X F).out 3 2).symm.mp hq

/-- On a locally Noetherian scheme a module of finite presentation is coherent. -/
private theorem coherent_of_finitePresentation {X : Scheme.{u}}
    [IsLocallyNoetherian X] (F : X.Modules) [F.IsFinitePresentation] :
    F.IsCoherent := by
  have hq : F.IsQuasicoherent ∧ F.IsFiniteType :=
    ((Stacks.AlgebraicGeometry.CoherenceCriteria.coherent_tfae X F).out 3 2).mp
      (show F.IsFinitePresentation from inferInstance)
  exact ((Stacks.AlgebraicGeometry.CoherenceCriteria.coherent_tfae X F).out 2 1).mp hq

/-- The cohomology of a two-periodic complex whose terms are isomorphic to a coherent sheaf is
again coherent. -/
theorem homology_isCoherent
    (C : ChowSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsCoherent]
    (K : CochainComplex X.Modules (ZMod 2))
    (e : ∀ i : ZMod 2, K.X i ≅ F) (i : ZMod 2) :
    (K.homology i).IsCoherent := by
  let : IsLocallyNoetherian X := by
    let : IsLocallyNoetherian C.S := C.isLocallyNoetherian
    exact LocallyOfFiniteType.isLocallyNoetherian f
  let hfp : F.IsFinitePresentation := finitePresentation_of_coherent F
  have hterm (j : ZMod 2) : (K.X j).IsCoherent := by
    let : F.IsFinitePresentation := hfp
    have hfpj : (K.X j).IsFinitePresentation :=
      (SheafOfModules.isFinitePresentation X.ringCatSheaf).prop_of_iso (e j).symm hfp
    let : (K.X j).IsFinitePresentation := hfpj
    exact coherent_of_finitePresentation (K.X j)
  let S := K.sc i
  have h₃ : S.X₃.IsCoherent := by
    change (K.X ((ComplexShape.up (ZMod 2)).next i)).IsCoherent
    simpa only [CochainComplex.next] using hterm (i + 1)
  have h₂ : S.X₂.IsCoherent := hterm i
  have h₁ : S.X₁.IsCoherent := by
    change (K.X ((ComplexShape.up (ZMod 2)).prev i)).IsCoherent
    simpa only [CochainComplex.prev] using hterm (i - 1)
  let : S.X₁.IsCoherent := h₁
  let : S.X₂.IsCoherent := h₂
  let : S.X₃.IsCoherent := h₃
  have hk : (kernel S.g).IsCoherent :=
    SheafOfModules.kernel_isCoherent S.g
  let : (kernel S.g).IsCoherent := hk
  let m := kernel.lift S.g S.f S.zero
  let : (cokernel m).IsCoherent :=
    SheafOfModules.cokernel_isCoherent m
  have hFP : (cokernel m).IsFinitePresentation :=
    finitePresentation_of_coherent (cokernel m)
  let : (cokernel m).IsFinitePresentation := hFP
  let H : S.homology ≅ cokernel m := S.homologyIsoCokernelLift
  have hFPH : S.homology.IsFinitePresentation :=
    (SheafOfModules.isFinitePresentation X.ringCatSheaf).prop_of_iso H.symm hFP
  let : S.homology.IsFinitePresentation := hFPH
  change S.homology.IsCoherent
  exact coherent_of_finitePresentation S.homology

/-- The abelian-group-valued stalk functor on sheaves of modules preserves finite limits. -/
private theorem stalkF_preservesFiniteLimits
    {X : AlgebraicGeometry.RingedSpace.{u, u}} (x : X.carrier) :
    PreservesFiniteLimits (stalkF x) := by
  unfold stalkF
  let F := SheafOfModules.toSheaf (structureSheafRing X)
  let G := TopCat.Sheaf.forget AddCommGrpCat.{u} X.carrier ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  have hF : PreservesFiniteLimits F := inferInstance
  have hG : PreservesFiniteLimits G := inferInstance
  exact @Limits.comp_preservesFiniteLimits _ _ _ _ _ _ F G hF hG

/-- The abelian-group-valued stalk functor on sheaves of modules preserves homology: it is exact,
being a composite of a left adjoint and a stalk functor. -/
private theorem stalkFunctor_preservesHomology
    {X : AlgebraicGeometry.RingedSpace.{u, u}} (x : X.carrier)
    (hzero : (stalkF x).PreservesZeroMorphisms) :
    (stalkF x).PreservesHomology := by
  classical
  let : (stalkF x).PreservesZeroMorphisms := hzero
  let hcolim : PreservesFiniteColimits (stalkF x) := by
    unfold stalkF
    exact compPFC
      (SheafOfModules.toSheaf (structureSheafRing X))
      (TopCat.Sheaf.forget AddCommGrpCat.{u} X.carrier ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)
      (toSheafColim X) (forgetStalkColim x)
  let : PreservesFiniteLimits (stalkF x) := stalkF_preservesFiniteLimits x
  let : PreservesFiniteColimits (stalkF x) := hcolim
  exact Functor.preservesHomologyOfExact (stalkF x)

/-- The abelian-group-valued stalk functor on sheaves of modules preserves zero morphisms. -/
private theorem stalkFunctor_preservesZeroMorphisms
    {X : AlgebraicGeometry.RingedSpace.{u, u}} (x : X.carrier) :
    (stalkF x).PreservesZeroMorphisms := by
  have hfirst :
      (SheafOfModules.toSheaf (structureSheafRing X)).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive _
  let : (SheafOfModules.toSheaf (structureSheafRing X)).PreservesZeroMorphisms := hfirst
  let G := TopCat.Sheaf.forget AddCommGrpCat.{u} X.carrier ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  let : (TopCat.Sheaf.forget AddCommGrpCat.{u} X.carrier).Additive := inferInstance
  let : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).Additive := inferInstance
  let : G.Additive := by infer_instance
  have hsecond : G.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_additive G
  let : G.PreservesZeroMorphisms := hsecond
  exact @Functor.preservesZeroMorphisms_comp _ _ _ _ _ _ _ _ _
    (SheafOfModules.toSheaf (structureSheafRing X)) G hfirst hsecond

/-- If the homology of a short complex of modules has vanishing stalk at a point, then the stalk
of the short complex at that point is exact. -/
private theorem stalkShortComplex_exact_of_homology_subsingleton
    {X : Scheme.{u}} (K : CochainComplex X.Modules (ZMod 2)) (i : ZMod 2) (x : X)
    [hzero : (stalkF (X := X.toRingedSpace) x).PreservesZeroMorphisms]
    (hsub : Subsingleton (abStalk (K.homology i) x)) :
    (@ShortComplex.map _ _ _ _ _ _ (K.sc i)
      (stalkF (X := X.toRingedSpace) x) hzero).Exact := by
  let : (stalkF (X := X.toRingedSpace) x).PreservesZeroMorphisms := hzero
  let : (stalkF (X := X.toRingedSpace) x).PreservesHomology :=
    stalkFunctor_preservesHomology (X := X.toRingedSpace) x
      (stalkFunctor_preservesZeroMorphisms (X := X.toRingedSpace) x)
  let S := K.sc i
  let F := stalkF (X := X.toRingedSpace) x
  have hPres : F.PreservesHomology :=
    stalkFunctor_preservesHomology (X := X.toRingedSpace) x
      (stalkFunctor_preservesZeroMorphisms (X := X.toRingedSpace) x)
  have hleft : F.PreservesLeftHomologyOf S :=
    @Functor.PreservesHomology.preservesLeftHomologyOf _ _ _ _ _ _ F hzero S hPres
  have hright : F.PreservesRightHomologyOf S :=
    @Functor.PreservesHomology.preservesRightHomologyOf _ _ _ _ _ _ F hzero S hPres
  let Smap : ShortComplex AddCommGrpCat :=
    @ShortComplex.map _ _ _ _ _ _ S F hzero
  let : S.HasHomology := inferInstance
  let : F.PreservesLeftHomologyOf S := hleft
  let : F.PreservesRightHomologyOf S := hright
  let : Smap.HasHomology := inferInstance
  have hhomzero : IsZero
      (F.obj S.homology) :=
    AddCommGrpCat.isZero_iff_subsingleton.mpr hsub
  have hmapzero : IsZero Smap.homology :=
    hhomzero.of_iso
      (@ShortComplex.mapHomologyIso _ _ _ _ _ _ S F hzero inferInstance inferInstance hleft)
  exact (ShortComplex.exact_iff_isZero_homology _).2 hmapzero

/-- The stalk functor at a point on `𝒪_X`-modules, valued in modules over the local ring of `X`
there. -/
private noncomputable abbrev moduleStalkFunctor {X : Scheme.{u}} (x : X) :
    X.Modules ⥤ ModuleCat.{u} (X.presheaf.stalk x) :=
  AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x ⋙
    ModuleCat.restrictScalars.{u, u}
      (SemilinearStalk.commStalkIso X.presheaf x).inv.hom

/-- The stalk functor on `𝒪_X`-modules is additive. -/
private theorem moduleStalkFunctor_additive {X : Scheme.{u}} (x : X) :
    (moduleStalkFunctor x).Additive := by
  let T := AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x
  let : PreservesBinaryBiproducts T :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts T
  let : T.Additive := Functor.additive_of_preservesBinaryBiproducts T
  let U := ModuleCat.restrictScalars.{u, u}
    (SemilinearStalk.commStalkIso X.presheaf x).inv.hom
  let : U.Additive := by
    change (ModuleCat.restrictScalars.{u, u}
      (SemilinearStalk.commStalkIso X.presheaf x).inv.hom).Additive
    infer_instance
  change (T ⋙ U).Additive
  constructor
  intro A B f g
  have h : U.map (T.map (f + g)) = U.map (T.map f) + U.map (T.map g) :=
    (congrArg U.map (T.map_add)).trans (U.map_add)
  exact h

/-- The stalk functor on `𝒪_X`-modules preserves homology. -/
private theorem moduleStalkFunctor_preservesHomology {X : Scheme.{u}} (x : X)
    [hadd : (moduleStalkFunctor x).Additive] :
    (moduleStalkFunctor x).PreservesHomology := by
  let T := moduleStalkFunctor x
  let U := forget₂ (ModuleCat.{u} (X.presheaf.stalk x)) AddCommGrpCat.{u}
  have hTU : PreservesFiniteLimits (T ⋙ U) :=
    stalkF_preservesFiniteLimits (X := X.toRingedSpace) x
  let : PreservesFiniteLimits (T ⋙ U) := hTU
  let : PreservesFiniteLimits T := preservesFiniteLimits_of_reflects_of_preserves T U
  let : PreservesFiniteColimits T := by
    let A := AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x
    let B := ModuleCat.restrictScalars.{u, u}
      (SemilinearStalk.commStalkIso X.presheaf x).inv.hom
    have hA : PreservesFiniteColimits A := inferInstance
    have hB : PreservesFiniteColimits B := inferInstance
    exact @Limits.comp_preservesFiniteColimits _ _ _ _ _ _ A B hA hB
  exact Functor.preservesHomologyOfExact T

/-- The action on a stalk of the stalk of the structure sheaf taken in `CommRingCat` agrees, along
the comparison isomorphism, with the action of the stalk taken in `RingCat`. -/
private theorem commStalk_smul_eq {X : Scheme.{u}} (F : X.Modules) (x : X)
    (r : TopCat.Presheaf.stalk (C := RingCat.{u})
      (X.presheaf ⋙ forget₂ CommRingCat RingCat) x)
    (m : TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) :
    letI : Module (X.presheaf.stalk x)
      (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) F.val x
    letI : Module (TopCat.Presheaf.stalk (C := RingCat.{u})
      (X.presheaf ⋙ forget₂ CommRingCat RingCat) x)
      (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) :=
      PresheafOfModules.instModuleCarrierStalkRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf ⋙ forget₂ CommRingCat RingCat) F.val x
    SemilinearStalk.commStalkRingEquiv X.presheaf x r • m = r • m := by
  let : Module (TopCat.Presheaf.stalk (C := RingCat.{u})
      (X.presheaf ⋙ forget₂ CommRingCat RingCat) x)
      (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) :=
    PresheafOfModules.instModuleCarrierStalkRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf ⋙ forget₂ CommRingCat RingCat) F.val x
  obtain ⟨U, hxU, a, ha⟩ := TopCat.Presheaf.exists_germ_eq
    (X.presheaf ⋙ forget₂ CommRingCat RingCat) r
  obtain ⟨V, hxV, b, hb⟩ := TopCat.Presheaf.exists_germ_eq F.val.presheaf m
  have hxW : x ∈ U ⊓ V := ⟨hxU, hxV⟩
  let aW := X.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op a
  let bW := F.val.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op b
  have haW : TopCat.Presheaf.germ (X.presheaf ⋙ forget₂ CommRingCat RingCat)
      (U ⊓ V) x hxW aW = r := by
    change TopCat.Presheaf.germ (X.presheaf ⋙ forget₂ CommRingCat RingCat) (U ⊓ V) x hxW
      ((X.presheaf ⋙ forget₂ CommRingCat RingCat).map
        (homOfLE (inf_le_left : U ⊓ V ≤ U)).op a) = r
    rw [TopCat.Presheaf.germ_res_apply]
    exact ha
  have hbW : TopCat.Presheaf.germ F.val.presheaf (U ⊓ V) x hxW bW = m := by
    rw [TopCat.Presheaf.germ_res_apply]
    exact hb
  rw [← haW, ← hbW, SemilinearStalk.commStalkRingEquiv_germ]
  exact (PresheafOfModules.germ_smul (R := X.presheaf) F.val x
    (U ⊓ V) hxW aW bW).symm.trans
      (PresheafOfModules.germ_ringCat_smul F.val x (U ⊓ V) hxW aW bW)

/-- The value of the stalk functor at a module is its stalk, carrying the canonical module
structure over the local ring. -/
private noncomputable def moduleStalkIso {X : Scheme.{u}} (F : X.Modules) (x : X) :
    letI := stalkModule (X := X.toRingedSpace) F x
    (moduleStalkFunctor x).obj F ≅
      ModuleCat.of (X.presheaf.stalk x) (abStalk F x) := by
  letI := stalkModule (X := X.toRingedSpace) F x
  letI : Module (TopCat.Presheaf.stalk (C := RingCat.{u})
      (X.presheaf ⋙ forget₂ CommRingCat RingCat) x)
      (abStalk F x) :=
    PresheafOfModules.instModuleCarrierStalkRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf ⋙ forget₂ CommRingCat RingCat) F.val x
  let e : (moduleStalkFunctor x).obj F ≃ₗ[X.presheaf.stalk x]
      ModuleCat.of (X.presheaf.stalk x) (abStalk F x) :=
    { toFun := fun z => z
      invFun := fun z => z
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := by
        intro r z
        change ((SemilinearStalk.commStalkIso X.presheaf x).inv.hom r •
          (show abStalk F x from z)) =
          (r • (show abStalk F x from z))
        have h := commStalk_smul_eq F x
          ((SemilinearStalk.commStalkIso X.presheaf x).inv.hom r) z
        have hscalar : SemilinearStalk.commStalkRingEquiv X.presheaf x
            ((SemilinearStalk.commStalkIso X.presheaf x).inv.hom r) = r :=
          (SemilinearStalk.commStalkRingEquiv X.presheaf x).apply_symm_apply r
        rw [hscalar] at h
        exact h.symm }
  exact e.toModuleIso

/-- At a point of relative dimension `k` lying on no component of the support of delta-dimension
`k + 1`, the stalk of a coherent sheaf has finite length. -/
private theorem isFiniteLength_stalk_of_not_mem_top_components
    (C : ChowSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsCoherent] (k : ℤ)
    [QuasiSober (SheafOfModules.supp F)]
    (hbound : ∀ y ∈ SheafOfModules.supp F,
      relativeDimension C.dimensionFunction f y ≤ k + 1)
    (x : X) (hxδ : relativeDimension C.dimensionFunction f x = k)
    (hnot : ∀ Z : irreducibleComponents (SheafOfModules.supp F : Set X),
      relativeDimension C.dimensionFunction f (Z.2.1.genericPoint).1 = k + 1 →
        x ∉ Subtype.val '' (Z : Set (SheafOfModules.supp F))) :
    letI := stalkModule (X := X.toRingedSpace) F x
    IsFiniteLength (X.presheaf.stalk x) (abStalk F x) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let := stalkModule (X := X.toRingedSpace) F x
  by_cases hx : x ∈ SheafOfModules.supp F
  · let Z : irreducibleComponents (SheafOfModules.supp F : Set X) :=
      ⟨irreducibleComponent ⟨x, hx⟩, irreducibleComponent_mem_irreducibleComponents _⟩
    have hxZ : x ∈ Subtype.val '' (Z : Set (SheafOfModules.supp F)) :=
      ⟨⟨x, hx⟩, mem_irreducibleComponent, rfl⟩
    have hη : IsGenericPoint (Z.2.1.genericPoint).1
        (Subtype.val '' (Z : Set (SheafOfModules.supp F))) := by
      let : F.IsFiniteType := isFiniteType_of_isCoherent F
      have hc := (SheafOfModules.isClosed_supp F).isClosedEmbedding_subtypeVal
      change closure ({(Z.2.1.genericPoint).1} : Set X) = _
      rw [← Set.image_singleton, hc.closure_image_eq,
        (Z.2.1.isGenericPoint_genericPoint
          (isClosed_of_mem_irreducibleComponents _ Z.2)).def]
    have hspec : (Z.2.1.genericPoint).1 ⤳ x := by
      rw [specializes_iff_mem_closure, hη.def]
      exact hxZ
    have heq : (Z.2.1.genericPoint).1 = x := by
      by_contra hne
      obtain ⟨d, hd⟩ := relativeDimension_isDimensionFunction
        C.isUniversallyCatenary C.dimensionFunction f
      have hlt := d.strictAnti_specializes hspec hne
      rw [hd, hd, hxδ] at hlt
      have hle := hbound (Z.2.1.genericPoint).1 (Z.2.1.genericPoint).2
      exact hnot Z (by omega) hxZ
    exact isFiniteLength_stalk_of_isGenericPoint_component_supp
      F Z x (heq ▸ hη)
  · have : Subsingleton (abStalk F x) := by
      apply not_nontrivial_iff_subsingleton.mp
      intro h
      exact hx ((SheafOfModules.mem_supp_iff_nontrivial_stalk F x).2 h)
    exact Module.length_ne_top_iff.mp (by simp)

/-- The complex of stalks at a point of a two-periodic complex of `𝒪_X`-modules. -/
private noncomputable abbrev moduleStalkComplex {X : Scheme.{u}}
    (K : CochainComplex X.Modules (ZMod 2)) (x : X) :
    CochainComplex (ModuleCat.{u} (X.presheaf.stalk x)) (ZMod 2) :=
  letI := moduleStalkFunctor_additive x
  ((moduleStalkFunctor x).mapHomologicalComplex (ComplexShape.up (ZMod 2))).obj K

/-- The cohomology of the complex of stalks is the stalk of the cohomology. -/
private noncomputable def moduleStalkHomologyIso {X : Scheme.{u}}
    (K : CochainComplex X.Modules (ZMod 2)) (x : X) (i : ZMod 2) :
    letI := stalkModule (X := X.toRingedSpace) (K.homology i) x
    (moduleStalkComplex K x).homology i ≅
      ModuleCat.of (X.presheaf.stalk x) (abStalk (K.homology i) x) := by
  letI := moduleStalkFunctor_additive x
  letI := moduleStalkFunctor_preservesHomology x
  exact ((K.sc i).mapHomologyIso (moduleStalkFunctor x)).trans
    (moduleStalkIso (K.homology i) x)

/-- The multiplicity of a cohomology sheaf at a point is the length of the cohomology of the
complex of stalks there. -/
private theorem sheafMultiplicity_eq_stalkComplexLength {X : Scheme.{u}}
    (K : CochainComplex X.Modules (ZMod 2)) (x : X) (i : ZMod 2) :
    sheafMultiplicity (K.homology i) x =
      ((Module.length (X.presheaf.stalk x)
        ((moduleStalkComplex K x).homology i)).toNat : ℤ) := by
  let := stalkModule (X := X.toRingedSpace) (K.homology i) x
  have h := (moduleStalkHomologyIso K x i).toLinearEquiv.length_eq
  exact congrArg (fun n : ℕ∞ => (n.toNat : ℤ)) h.symm

/-- The difference of the two multiplicities at a point is the periodic length of the complex of
stalks there. -/
private theorem sheafMultiplicity_sub_eq_periodicLength {X : Scheme.{u}}
    (K : CochainComplex X.Modules (ZMod 2)) (x : X) :
    sheafMultiplicity (K.homology 0) x -
      sheafMultiplicity (K.homology 1) x =
        AlgebraicGeometry.periodicLength (moduleStalkComplex K x) := by
  rw [sheafMultiplicity_eq_stalkComplexLength,
    sheafMultiplicity_eq_stalkComplexLength]

/-- At a point where the stalk of the sheaf has finite length the two cohomology multiplicities
agree. -/
private theorem sheafMultiplicity_sub_eq_zero_of_finiteLength {X : Scheme.{u}}
    (F : X.Modules) (K : CochainComplex X.Modules (ZMod 2))
    (e : ∀ i : ZMod 2, K.X i ≅ F) (x : X)
    (hfin : letI := stalkModule (X := X.toRingedSpace) F x
      IsFiniteLength (X.presheaf.stalk x) (abStalk F x)) :
    sheafMultiplicity (K.homology 0) x -
      sheafMultiplicity (K.homology 1) x = 0 := by
  let := stalkModule (X := X.toRingedSpace) F x
  rw [sheafMultiplicity_sub_eq_periodicLength]
  let T := moduleStalkFunctor x
  let := moduleStalkFunctor_additive x
  let e₀ := (T.mapIso (e 0)).trans (moduleStalkIso F x)
  have h₀ : IsFiniteLength (X.presheaf.stalk x) ((moduleStalkComplex K x).X 0) := by
    apply Module.length_ne_top_iff.mp
    change Module.length (X.presheaf.stalk x) (T.obj (K.X 0)) ≠ ⊤
    rw [e₀.toLinearEquiv.length_eq]
    exact Module.length_ne_top_iff.mpr hfin
  exact AlgebraicGeometry.periodicLength_eq_zero_of_iso (moduleStalkComplex K x) h₀
    (T.mapIso ((e 0).trans (e 1).symm))

/-- At a point of relative dimension `k` the cohomology of the complex of stalks has finite
length. -/
private theorem moduleStalkComplex_homology_isFiniteLength
    (C : ChowSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsCoherent]
    (K : CochainComplex X.Modules (ZMod 2))
    (e : ∀ i : ZMod 2, K.X i ≅ F) (k : ℤ)
    (hHk : ∀ (i : ZMod 2) (x : X),
      x ∈ SheafOfModules.supp (K.homology i) →
        relativeDimension C.dimensionFunction f x ≤ k)
    (x : X) (hx : relativeDimension C.dimensionFunction f x = k)
    (i : ZMod 2) :
    IsFiniteLength (X.presheaf.stalk x) ((moduleStalkComplex K x).homology i) := by
  let : (K.homology i).IsCoherent := homology_isCoherent C f F K e i
  have dHi := schemeDeltaDimension_reducedSupport_le_of_pointwise C f
    (K.homology i) k (hHk i)
  have hfin := isFiniteLength_stalk_of_relativeDimension_eq C f
    (K.homology i) dHi hx
  let := stalkModule (X := X.toRingedSpace) (K.homology i) x
  apply Module.length_ne_top_iff.mp
  rw [(moduleStalkHomologyIso K x i).toLinearEquiv.length_eq]
  exact Module.length_ne_top_iff.mpr hfin

/-- Above the dimension bound on the cohomology sheaves their stalks vanish. -/
private theorem homology_stalk_subsingleton_of_relativeDimension_gt
    (C : ChowSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (K : CochainComplex X.Modules (ZMod 2)) (i : ZMod 2)
    (x : X) (k : ℤ)
    (hHk : ∀ (i : ZMod 2) (x : X),
      x ∈ SheafOfModules.supp (K.homology i) →
        relativeDimension C.dimensionFunction f x ≤ k)
    (hgt : k < relativeDimension C.dimensionFunction f x) :
    Subsingleton (abStalk (K.homology i) x) := by
  have hnot : ¬ Nontrivial ((K.homology i).presheaf.stalk x) := by
    intro hnontrivial
    have hx : x ∈ SheafOfModules.supp (K.homology i) :=
      (SheafOfModules.mem_supp_iff_nontrivial_stalk
        (K.homology i) x).2 hnontrivial
    exact (not_le_of_gt hgt) (hHk i x hx)
  change Subsingleton ((K.homology i).presheaf.stalk x)
  exact not_nontrivial_iff_subsingleton.mp hnot

/-- The isomorphism of stalks induced by an isomorphism of `𝒪_X`-modules, as an isomorphism of
abelian groups. -/
private noncomputable def stalkEquivOfIso {X : Scheme.{u}} {L M : X.Modules}
    (e : L ≅ M) (x : X) :
    abStalk L x ≃+ abStalk M x := by
  let es := (stalkF (X := X.toRingedSpace) x).mapIso e
  exact es.addCommGroupIsoToAddEquiv

/-- Transport of the chosen isomorphisms of the terms of a complex along an equality of degrees. -/
private theorem complexTermIso_transport {X : Scheme.{u}}
    (K : CochainComplex X.Modules (ZMod 2)) (F : X.Modules)
    (e : ∀ i : ZMod 2, K.X i ≅ F) {i j : ZMod 2} (h : i = j) :
    e i = (K.XIsoOfEq h).trans (e j) := by
  cases h
  simp

/-- The stalk functor at `x` carries a composite of three maps of `𝒪_X`-modules to the
composite of their stalk maps. -/
private theorem stalkF_map_comp₃ {X : Scheme.{u}} (x : X) {A B C D : X.Modules}
    (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D) :
    (stalkF (X := X.toRingedSpace) x).map (a ≫ b ≫ c) =
      (stalkF (X := X.toRingedSpace) x).map a ≫
        (stalkF (X := X.toRingedSpace) x).map b ≫
          (stalkF (X := X.toRingedSpace) x).map c :=
  ((stalkF (X := X.toRingedSpace) x).map_comp a (b ≫ c)).trans
    (congrArg (fun q => (stalkF (X := X.toRingedSpace) x).map a ≫ q)
      ((stalkF (X := X.toRingedSpace) x).map_comp b c))

/-- The stalk isomorphism of a composite of isomorphisms is the composite of the stalk
isomorphisms. -/
private theorem stalkEquivOfIso_trans {X : Scheme.{u}} {L M N : X.Modules}
    (e : L ≅ M) (f : M ≅ N) (x : X) :
    stalkEquivOfIso (e.trans f) x = (stalkEquivOfIso e x).trans (stalkEquivOfIso f x) := by
  ext z
  exact congrArg (fun q => (ConcreteCategory.hom q) z)
    ((stalkF (X := X.toRingedSpace) x).map_comp e.hom f.hom)

/-- The underlying additive map of the stalk isomorphism of an isomorphism is the stalk map of
that isomorphism. -/
private theorem stalkEquivOfIso_toAddMonoidHom {X : Scheme.{u}} {L M : X.Modules}
    (e : L ≅ M) (x : X) :
    (stalkEquivOfIso e x).toAddMonoidHom =
      (stalkLinearMap (X := X.toRingedSpace) e.hom x).toAddMonoidHom := by
  ext z
  rfl

/-- The two endomorphisms of the stalk obtained by conjugating the differentials of a two-periodic
complex with the chosen isomorphisms of its terms, as additive maps. -/
private noncomputable def periodicStalkMaps {X : Scheme.{u}}
    (F : X.Modules) (K : CochainComplex X.Modules (ZMod 2))
    (e : ∀ i : ZMod 2, K.X i ≅ F) (x : X) :
    AddMonoid.End (abStalk F x) × AddMonoid.End (abStalk F x) := by
  let S₀ := K.sc (0 : ZMod 2)
  let M₀ := @ShortComplex.map _ _ _ _ _ _ S₀ (stalkF (X := X.toRingedSpace) x)
    (stalkFunctor_preservesZeroMorphisms (X := X.toRingedSpace) x)
  let e₀ := stalkEquivOfIso (e 0) x
  let eNext := stalkEquivOfIso
    (e ((ComplexShape.up (ZMod 2)).next (0 : ZMod 2))) x
  let ePrev := stalkEquivOfIso
    (e ((ComplexShape.up (ZMod 2)).prev (0 : ZMod 2))) x
  let φ : AddMonoid.End (abStalk F x) :=
    eNext.toAddMonoidHom.comp
      (M₀.g.hom.comp e₀.symm.toAddMonoidHom)
  let ψ : AddMonoid.End (abStalk F x) :=
    e₀.toAddMonoidHom.comp
      (M₀.f.hom.comp ePrev.symm.toAddMonoidHom)
  exact (φ, ψ)

private theorem up_zmod_two_prev_zero : (ComplexShape.up (ZMod 2)).prev (0 : ZMod 2) = 1 :=
  (ComplexShape.up (ZMod 2)).prev_eq' (by decide)

private theorem up_zmod_two_next_zero : (ComplexShape.up (ZMod 2)).next (0 : ZMod 2) = 1 :=
  (ComplexShape.up (ZMod 2)).next_eq' (by decide)

private theorem up_zmod_two_prev_one : (ComplexShape.up (ZMod 2)).prev (1 : ZMod 2) = 0 :=
  (ComplexShape.up (ZMod 2)).prev_eq' (by decide)

private theorem up_zmod_two_next_one : (ComplexShape.up (ZMod 2)).next (1 : ZMod 2) = 0 :=
  (ComplexShape.up (ZMod 2)).next_eq' (by decide)

/-- Transport of the stalk isomorphisms of the terms of a complex along an equality of
degrees. -/
private theorem stalkEquivOfIso_complexTerm {X : Scheme.{u}}
    (K : CochainComplex X.Modules (ZMod 2)) (F : X.Modules)
    (e : ∀ i : ZMod 2, K.X i ≅ F) (x : X) {i j : ZMod 2} (h : i = j) :
    stalkEquivOfIso (e i) x =
      (stalkEquivOfIso (K.XIsoOfEq h) x).trans (stalkEquivOfIso (e j) x) := by
  rw [complexTermIso_transport K F e h]
  exact stalkEquivOfIso_trans _ _ _

/-- Conjugating the stalk map of a differential by the transport isomorphisms along equalities of
degrees gives the stalk map of the transported differential. -/
private theorem stalkF_map_d_transport {X : Scheme.{u}}
    (K : CochainComplex X.Modules (ZMod 2)) (x : X) {i j i' j' : ZMod 2}
    (h₁ : i' = i) (h₂ : j = j') :
    (stalkEquivOfIso (K.XIsoOfEq h₂) x).toAddMonoidHom.comp
      (((stalkF (X := X.toRingedSpace) x).map (K.d i j)).hom.comp
        (stalkEquivOfIso (K.XIsoOfEq h₁) x).toAddMonoidHom) =
      ((stalkF (X := X.toRingedSpace) x).map (K.d i' j')).hom := by
  have hD : (K.XIsoOfEq h₁).hom ≫ K.d i j ≫ (K.XIsoOfEq h₂).hom = K.d i' j' := by
    rw [← Category.assoc, K.XIsoOfEq_hom_comp_d h₁, K.d_comp_XIsoOfEq_hom h₂]
  rw [stalkEquivOfIso_toAddMonoidHom, stalkEquivOfIso_toAddMonoidHom]
  exact congrArg (fun q => q.hom)
    ((stalkF_map_comp₃ x (K.XIsoOfEq h₁).hom (K.d i j) (K.XIsoOfEq h₂).hom).symm.trans
      (congrArg (fun q => (stalkF (X := X.toRingedSpace) x).map q) hD))

/-- The two conjugated endomorphisms of the stalk form an exact pair, in the order through degree
zero, as soon as the cohomology sheaf in degree zero has vanishing stalk at the point. -/
private theorem periodicStalkMaps_exact_zero {X : Scheme.{u}}
    (F : X.Modules) (K : CochainComplex X.Modules (ZMod 2))
    (e : ∀ i : ZMod 2, K.X i ≅ F) (x : X)
    (hsub₀ : Subsingleton (abStalk (K.homology (0 : ZMod 2)) x)) :
    Function.Exact (periodicStalkMaps F K e x).2 (periodicStalkMaps F K e x).1 := by
  let : (stalkF (X := X.toRingedSpace) x).PreservesZeroMorphisms :=
    stalkFunctor_preservesZeroMorphisms (X := X.toRingedSpace) x
  let M₀ := @ShortComplex.map _ _ _ _ _ _ (K.sc (0 : ZMod 2)) (stalkF x)
    (stalkFunctor_preservesZeroMorphisms (X := X.toRingedSpace) x)
  have hfun₀ : Function.Exact M₀.f.hom M₀.g.hom :=
    (ShortComplex.ab_exact_iff_function_exact M₀).mp
      (stalkShortComplex_exact_of_homology_subsingleton K 0 x hsub₀)
  let ePrev := stalkEquivOfIso
    (e ((ComplexShape.up (ZMod 2)).prev (0 : ZMod 2))) x
  let eMid := stalkEquivOfIso (e 0) x
  let eNext := stalkEquivOfIso
    (e ((ComplexShape.up (ZMod 2)).next (0 : ZMod 2))) x
  have hsquare₀f :
      (eMid.toAddMonoidHom.comp (M₀.f.hom.comp ePrev.symm.toAddMonoidHom)).comp
        ePrev.toAddMonoidHom = eMid.toAddMonoidHom.comp M₀.f.hom := by
    ext z
    change eMid (M₀.f.hom (ePrev.symm (ePrev z))) = eMid (M₀.f.hom z)
    rw [ePrev.symm_apply_apply]
  have hsquare₀g :
      (eNext.toAddMonoidHom.comp (M₀.g.hom.comp eMid.symm.toAddMonoidHom)).comp
        eMid.toAddMonoidHom = eNext.toAddMonoidHom.comp M₀.g.hom := by
    ext z
    change eNext (M₀.g.hom (eMid.symm (eMid z))) = eNext (M₀.g.hom z)
    rw [eMid.symm_apply_apply]
  exact (Function.Exact.iff_of_ladder_addEquiv
    ePrev eMid eNext hsquare₀f hsquare₀g).mpr hfun₀

/-- The two conjugated endomorphisms of the stalk form an exact pair, in the order through degree
one, as soon as the cohomology sheaf in degree one has vanishing stalk at the point. -/
private theorem periodicStalkMaps_exact_one {X : Scheme.{u}}
    (F : X.Modules) (K : CochainComplex X.Modules (ZMod 2))
    (e : ∀ i : ZMod 2, K.X i ≅ F) (x : X)
    (hsub₁ : Subsingleton (abStalk (K.homology (1 : ZMod 2)) x)) :
    Function.Exact (periodicStalkMaps F K e x).1 (periodicStalkMaps F K e x).2 := by
  let : (stalkF (X := X.toRingedSpace) x).PreservesZeroMorphisms :=
    stalkFunctor_preservesZeroMorphisms (X := X.toRingedSpace) x
  let P := periodicStalkMaps F K e x
  let M₀ := @ShortComplex.map _ _ _ _ _ _ (K.sc (0 : ZMod 2)) (stalkF x)
    (stalkFunctor_preservesZeroMorphisms (X := X.toRingedSpace) x)
  let M₁ := @ShortComplex.map _ _ _ _ _ _ (K.sc (1 : ZMod 2)) (stalkF x)
    (stalkFunctor_preservesZeroMorphisms (X := X.toRingedSpace) x)
  have hfun₁ : Function.Exact M₁.f.hom M₁.g.hom :=
    (ShortComplex.ab_exact_iff_function_exact M₁).mp
      (stalkShortComplex_exact_of_homology_subsingleton K 1 x hsub₁)
  let ePrev := stalkEquivOfIso
    (e ((ComplexShape.up (ZMod 2)).prev (0 : ZMod 2))) x
  let eMid := stalkEquivOfIso (e 0) x
  let eNext := stalkEquivOfIso
    (e ((ComplexShape.up (ZMod 2)).next (0 : ZMod 2))) x
  have hPform : P =
      (eNext.toAddMonoidHom.comp (M₀.g.hom.comp eMid.symm.toAddMonoidHom),
       eMid.toAddMonoidHom.comp (M₀.f.hom.comp ePrev.symm.toAddMonoidHom)) := rfl
  let ePrev₁ := stalkEquivOfIso
    (e ((ComplexShape.up (ZMod 2)).prev (1 : ZMod 2))) x
  let eMid₁ := stalkEquivOfIso (e 1) x
  let eNext₁ := stalkEquivOfIso
    (e ((ComplexShape.up (ZMod 2)).next (1 : ZMod 2))) x
  let tPrev1 := stalkEquivOfIso (K.XIsoOfEq up_zmod_two_prev_one) x
  let tNext0 := stalkEquivOfIso (K.XIsoOfEq up_zmod_two_next_zero) x
  let tPrev0 := stalkEquivOfIso (K.XIsoOfEq up_zmod_two_prev_zero) x
  let tNext1 := stalkEquivOfIso (K.XIsoOfEq up_zmod_two_next_one) x
  have hePrev1 : ePrev₁ = tPrev1.trans eMid := stalkEquivOfIso_complexTerm K F e x _
  have heNext0 : eNext = tNext0.trans eMid₁ := stalkEquivOfIso_complexTerm K F e x _
  have hePrev0 : ePrev = tPrev0.trans eMid₁ := stalkEquivOfIso_complexTerm K F e x _
  have heNext1 : eNext₁ = tNext1.trans eMid := stalkEquivOfIso_complexTerm K F e x _
  have hsquare₁f : P.1.comp ePrev₁.toAddMonoidHom =
      eMid₁.toAddMonoidHom.comp M₁.f.hom := by
    rw [hPform, hePrev1, heNext0]
    ext z
    change eMid₁ (tNext0 (M₀.g.hom (eMid.symm (eMid (tPrev1 z))))) = _
    rw [eMid.symm_apply_apply]
    exact congrArg eMid₁ (DFunLike.congr_fun
      (stalkF_map_d_transport K x up_zmod_two_prev_one up_zmod_two_next_zero) z)
  have hsquare₁g : P.2.comp eMid₁.toAddMonoidHom =
      eNext₁.toAddMonoidHom.comp M₁.g.hom := by
    rw [hPform, hePrev0, heNext1]
    ext z
    change eMid (M₀.f.hom (tPrev0.symm (eMid₁.symm (eMid₁ z)))) = _
    rw [eMid₁.symm_apply_apply]
    have hz := DFunLike.congr_fun
      (stalkF_map_d_transport K x up_zmod_two_prev_zero up_zmod_two_next_one) (tPrev0.symm z)
    change tNext1 (M₁.g.hom (tPrev0 (tPrev0.symm z))) =
      M₀.f.hom (tPrev0.symm z) at hz
    rw [tPrev0.apply_symm_apply] at hz
    exact congrArg eMid hz.symm
  exact (Function.Exact.iff_of_ladder_addEquiv
    ePrev₁ eMid₁ eNext₁ hsquare₁f hsquare₁g).mpr hfun₁

/-- The two conjugated endomorphisms of the stalk form an exact pair in both orders as soon as
both cohomology sheaves have vanishing stalk at the point. -/
private theorem periodicStalkMaps_exact {X : Scheme.{u}}
    (F : X.Modules) (K : CochainComplex X.Modules (ZMod 2))
    (e : ∀ i : ZMod 2, K.X i ≅ F) (x : X)
    (hsub₀ : Subsingleton (abStalk (K.homology (0 : ZMod 2)) x))
    (hsub₁ : Subsingleton (abStalk (K.homology (1 : ZMod 2)) x)) :
    Function.Exact (periodicStalkMaps F K e x).2 (periodicStalkMaps F K e x).1 ∧
      Function.Exact (periodicStalkMaps F K e x).1 (periodicStalkMaps F K e x).2 :=
  ⟨periodicStalkMaps_exact_zero F K e x hsub₀, periodicStalkMaps_exact_one F K e x hsub₁⟩

/-- The linear stalk equivalence of an isomorphism has the additive stalk isomorphism as its
underlying additive equivalence. -/
private theorem stalkLinearEquivOfIso_toAddEquiv {X : Scheme.{u}} {L M : X.Modules}
    (e : L ≅ M) (x : X) :
    letI := stalkModule (X := X.toRingedSpace) L x
    letI := stalkModule (X := X.toRingedSpace) M x
    (stalkLinearEquivOfIso e x).toAddEquiv = stalkEquivOfIso e x := by
  let := stalkModule (X := X.toRingedSpace) L x
  let := stalkModule (X := X.toRingedSpace) M x
  ext z
  rfl

/-- The two conjugated endomorphisms of the stalk, as linear maps over the local ring. -/
private noncomputable def periodicStalkLinearMaps {X : Scheme.{u}}
    (F : X.Modules) (K : CochainComplex X.Modules (ZMod 2))
    (e : ∀ i : ZMod 2, K.X i ≅ F) (x : X) :
    letI := stalkModule (X := X.toRingedSpace) F x
    Module.End (X.presheaf.stalk x) (abStalk F x) ×
      Module.End (X.presheaf.stalk x) (abStalk F x) := by
  letI := stalkModule (X := X.toRingedSpace) F x
  letI (i : ZMod 2) := stalkModule (X := X.toRingedSpace) (K.X i) x
  let e₀ := stalkLinearEquivOfIso (e 0) x
  let eNext := stalkLinearEquivOfIso
    (e ((ComplexShape.up (ZMod 2)).next (0 : ZMod 2))) x
  let ePrev := stalkLinearEquivOfIso
    (e ((ComplexShape.up (ZMod 2)).prev (0 : ZMod 2))) x
  exact
    (eNext.toLinearMap ∘ₗ stalkLinearMap (K.sc 0).g x ∘ₗ
        e₀.symm.toLinearMap,
     e₀.toLinearMap ∘ₗ stalkLinearMap (K.sc 0).f x ∘ₗ
        ePrev.symm.toLinearMap)

/-- Their underlying additive maps are the two conjugated additive endomorphisms. -/
private theorem periodicStalkLinearMaps_toAddMonoidHom {X : Scheme.{u}}
    (F : X.Modules) (K : CochainComplex X.Modules (ZMod 2))
    (e : ∀ i : ZMod 2, K.X i ≅ F) (x : X) :
    ((periodicStalkLinearMaps F K e x).1.toAddMonoidHom,
      (periodicStalkLinearMaps F K e x).2.toAddMonoidHom) =
        periodicStalkMaps F K e x := by
  have hsymm {A B : X.Modules} (e' : A ≅ B) (z : abStalk B x) :
      letI := stalkModule (X := X.toRingedSpace) A x
      letI := stalkModule (X := X.toRingedSpace) B x
      (stalkLinearEquivOfIso e' x).symm z = (stalkEquivOfIso e' x).symm z := by
    let := stalkModule (X := X.toRingedSpace) A x
    let := stalkModule (X := X.toRingedSpace) B x
    exact DFunLike.congr_fun
      (congrArg AddEquiv.symm (stalkLinearEquivOfIso_toAddEquiv e' x)) z
  apply Prod.ext
  · ext z
    change stalkEquivOfIso _ x
      ((stalkLinearMap (K.sc 0).g x) ((stalkLinearEquivOfIso (e 0) x).symm z)) = _
    rw [hsymm]
    rfl
  · ext z
    change stalkEquivOfIso _ x
      ((stalkLinearMap (K.sc 0).f x) ((stalkLinearEquivOfIso
        (e ((ComplexShape.up (ZMod 2)).prev (0 : ZMod 2))) x).symm z)) = _
    rw [hsymm]
    rfl

/-- The two conjugated linear endomorphisms of the stalk form an exact pair in both orders as soon
as both cohomology sheaves have vanishing stalk at the point. -/
private theorem periodicStalkLinearMaps_exact {X : Scheme.{u}}
    (F : X.Modules) (K : CochainComplex X.Modules (ZMod 2))
    (e : ∀ i : ZMod 2, K.X i ≅ F) (x : X)
    (hsub₀ : Subsingleton (abStalk (K.homology (0 : ZMod 2)) x))
    (hsub₁ : Subsingleton (abStalk (K.homology (1 : ZMod 2)) x)) :
    Function.Exact (periodicStalkLinearMaps F K e x).1
        (periodicStalkLinearMaps F K e x).2 ∧
      Function.Exact (periodicStalkLinearMaps F K e x).2
        (periodicStalkLinearMaps F K e x).1 := by
  have h := periodicStalkMaps_exact F K e x hsub₀ hsub₁
  have heq := periodicStalkLinearMaps_toAddMonoidHom F K e x
  have h₁ : (periodicStalkLinearMaps F K e x).1.toAddMonoidHom =
      (periodicStalkMaps F K e x).1 := congrArg Prod.fst heq
  have h₂ : (periodicStalkLinearMaps F K e x).2.toAddMonoidHom =
      (periodicStalkMaps F K e x).2 := congrArg Prod.snd heq
  change Function.Exact (periodicStalkLinearMaps F K e x).1.toAddMonoidHom
      (periodicStalkLinearMaps F K e x).2.toAddMonoidHom ∧
    Function.Exact (periodicStalkLinearMaps F K e x).2.toAddMonoidHom
      (periodicStalkLinearMaps F K e x).1.toAddMonoidHom
  rw [h₁, h₂]
  exact h.symm

/-- A two-periodic complex of modules all of whose terms are isomorphic to a fixed module is
isomorphic to the two-periodic complex built from the conjugated differentials. -/
private theorem exists_twoPeriodicComplex_iso
    {R : Type*} [Ring R] (L : CochainComplex (ModuleCat.{u} R) (ZMod 2))
    (M : ModuleCat.{u} R) (e : ∀ i : ZMod 2, L.X i ≅ M) :
    let φ := ((e 0).inv ≫ L.d 0 1 ≫ (e 1).hom).hom
    let ψ := ((e 1).inv ≫ L.d 1 0 ≫ (e 0).hom).hom
    ∃ (hφψ : φ * ψ = 0) (hψφ : ψ * φ = 0),
      Nonempty (L ≅ AlgebraicGeometry.twoPeriodicComplex φ ψ hφψ hψφ) := by
  let φ := ((e 0).inv ≫ L.d 0 1 ≫ (e 1).hom).hom
  let ψ := ((e 1).inv ≫ L.d 1 0 ≫ (e 0).hom).hom
  have hcomp (a b c : ZMod 2) :
      ((e a).inv ≫ L.d a b ≫ (e b).hom) ≫ ((e b).inv ≫ L.d b c ≫ (e c).hom) = 0 := by
    simp only [Category.assoc, Iso.hom_inv_id_assoc, L.d_comp_d_assoc, zero_comp, comp_zero]
  have hφψ : φ * ψ = 0 := congrArg ModuleCat.Hom.hom (hcomp 1 0 1)
  have hψφ : ψ * φ = 0 := congrArg ModuleCat.Hom.hom (hcomp 0 1 0)
  refine ⟨hφψ, hψφ, ⟨HomologicalComplex.Hom.isoOfComponents e ?_⟩⟩
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact False.elim ((by decide : ¬ (ComplexShape.up (ZMod 2)).Rel 0 0) hij)
  · change (e 0).hom ≫ ((e 0).inv ≫ L.d 0 1 ≫ (e 1).hom) = _
    simp only [Iso.hom_inv_id_assoc]
    rfl
  · change (e 1).hom ≫ ((e 1).inv ≫ L.d 1 0 ≫ (e 0).hom) = _
    simp only [Iso.hom_inv_id_assoc]
    rfl
  · exact False.elim ((by decide : ¬ (ComplexShape.up (ZMod 2)).Rel 1 1) hij)

end Stacks.Chow
