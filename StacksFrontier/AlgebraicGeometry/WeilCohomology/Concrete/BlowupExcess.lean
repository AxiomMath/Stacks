module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.Blowup
public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.BlowupFormula
public import StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.DualTotalChern
public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.Factorization
public import StacksFrontier.AlgebraicGeometry.Conormal.SquareEpi
public import StacksFrontier.AlgebraicGeometry.ConormalSourceTransport.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.EtaQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Blowup.AdmissibleDominating
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.BlowupDimension
public import StacksFrontier.AlgebraicGeometry.ConormalSequenceRight.ConormalRank
public import StacksFrontier.AlgebraicGeometry.ConormalComparison.DefiningIdealConormalBridge
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleSplitting.KernelConstantRankGeneral
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleSplitting.KernelConstantRank
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleQuotients.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleCompare
public import StacksFrontier.AlgebraicGeometry.Chow.DiagonalVirtualNormalBundle
public import StacksFrontier.AlgebraicGeometry.Chow.SubbundleTopChernClass
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The excess bundle of the blowing up in a smooth centre

For a closed immersion `i : Z ⟶ X` of smooth projective schemes over `k`, with blowing up
`b : X' ⟶ X`, exceptional divisor `j : E ⟶ X'` and `π : E ⟶ Z`, the sheaf
`𝓕 = Ker(π^*𝒞_{Z/X} ⟶ 𝒞_{E/X'})` of Tag 0FVA (`Stacks.Chow.blowupExcessConormal`) is finite
locally free, and so is its dual `𝓕^∨`. This file records that, and names the class
`c_{r-1}(𝓕^∨) ∩ [E]` of Lemma 0FIH: the cap product of the Chern class `c_{r-1}(𝓕^∨)`
(`Stacks.Chow.totalChernOfFiniteLocallyFree`, Stacks 0ESW) with the fundamental class of `E` in
dimension `m`.

## Main definitions

* `Stacks.WeilCohomology.SmoothProjectiveScheme.excessConormal`: `𝓕`.
* `Stacks.WeilCohomology.SmoothProjectiveScheme.excessChernCap`: `c_{r-1}(𝓕^∨) ∩ [E]_m`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Chow

universe u

namespace Stacks.WeilCohomology.SmoothProjectiveScheme

open Stacks.AlgebraicGeometry.ReflexiveModules (dualSheaf)

variable {k : Type u} [Field k] {Z X : (SmoothProjectiveScheme k).FullSubcategory} (i : Z ⟶ X)
  [IsClosedImmersion i.hom.left]

/-- The Gysin map of Stacks 0FF3 exists for the blowing up `b`, a morphism between schemes smooth
over `k`. -/
theorem gysinMapExists_blowupHom : GysinMapExists (blowupHom i).hom.left :=
  GysinMapExists.of_smooth_source _ X.obj.hom (blowupObj i).obj.hom rfl

/-- **The sheaf `𝓕 = Ker(π^*𝒞_{Z/X} ⟶ 𝒞_{E/X'})` of Tag 0FVA**, on the exceptional divisor. -/
abbrev excessConormal : (exceptionalObj i).obj.left.Modules :=
  blowupExcessConormal i.hom.left

/-- The excess conormal sheaf `𝓕` is finite locally free. -/
instance isFiniteLocallyFree_excessConormal :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (excessConormal i) :=
  isFiniteLocallyFree_blowupExcessConormal i.hom.left (isRegularImmersion_of_isClosedImmersion i)
    (gysinMapExists_blowupHom i)

/-- The dual `𝓕^∨` of the excess conormal sheaf is finite locally free. -/
instance isFiniteLocallyFree_dualSheaf_excessConormal :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (dualSheaf (excessConormal i)) :=
  Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFree_dualSheaf _
    (isFiniteLocallyFree_excessConormal i)

/-- **The class `c_{r-1}(𝓕^∨) ∩ [E]_m`** of Lemma 0FIH, in `CH_{m-(r-1)}(E)`: the Chern class
`c_{r-1}` of the dual of the excess conormal sheaf capped with the fundamental class of `E` in
dimension `m`. -/
def excessChernCap (r : ℕ) (m : ℤ) :
    chowGroup (fieldChowSituation k) (exceptionalObj i).obj.hom (m - ((r - 1 : ℕ) : ℤ)) :=
  chowCohomologyCap (fieldChowSituation k) (gysinSystemOfInvertible _) (exceptionalObj i).obj.hom
    (((r - 1 : ℕ) : ℤ))
    (totalChernOfFiniteLocallyFree (fieldChowSituation k) (exceptionalObj i).obj.hom
      (dualSheaf (excessConormal i)) (r - 1)) m
    (fundamentalChowClass (fieldChowSituation k) (exceptionalObj i).obj.hom m)

/-! ### The excess conormal sequence `0 ⟶ 𝓕 ⟶ π^*𝒞_{Z/X} ⟶ 𝒞_{E/X'} ⟶ 0` -/

open Stacks.Immersion Stacks.ClosedImmersion in
/-- **The conormal sheaf `𝒞_{Z/X}`** of the centre, in the presentation of
`Stacks.Immersion.immersionConormalSheafMap`: the pullback along the closed factor `i.liftCoborder`
of its ideal sheaf. -/
abbrev centreConormal : Z.obj.left.Modules :=
  conormalSheaf i.hom.left.liftCoborder.toLRSHom.toShHom

open Stacks.Immersion Stacks.ClosedImmersion in
/-- **The conormal sheaf `𝒞_{E/X'}`** of the exceptional divisor, in the same presentation. -/
abbrev exceptionalConormal : (exceptionalObj i).obj.left.Modules :=
  conormalSheaf (exceptionalHom i).hom.left.liftCoborder.toLRSHom.toShHom

open Stacks.Immersion in
/-- The canonical map `π^*𝒞_{Z/X} ⟶ 𝒞_{E/X'}` of Tag 01R4 for the exceptional square. -/
abbrev excessConormalMap :
    (Scheme.Modules.pullback (exceptionalProj i).hom.left).obj (centreConormal i) ⟶
      exceptionalConormal i :=
  immersionConormalSheafMap (pullback.fst (Stacks.Blowup.blowUpToBase i.hom.left.ker) i.hom.left)
    i.hom.left (pullback.snd (Stacks.Blowup.blowUpToBase i.hom.left.ker) i.hom.left)
    (Stacks.Blowup.blowUpToBase i.hom.left.ker) (toShHom_square pullback.condition)

open Stacks.Immersion in
/-- **`π^*𝒞_{Z/X} ⟶ 𝒞_{E/X'}` is an epimorphism** (Tag 0473: for a cartesian square of immersions
the map of conormal sheaves is surjective). -/
instance epi_excessConormalMap : Epi (excessConormalMap i) :=
  epi_immersionConormalSheafMap _ _ _ _ (IsPullback.of_hasPullback _ _)

/-- **The excess conormal sequence** `0 ⟶ 𝓕 ⟶ π^*𝒞_{Z/X} ⟶ 𝒞_{E/X'} ⟶ 0` on `E`, `𝓕` being the
kernel. -/
abbrev excessShortComplex : ShortComplex (exceptionalObj i).obj.left.Modules :=
  ShortComplex.mk (kernel.ι (excessConormalMap i)) (excessConormalMap i) (kernel.condition _)

/-- The first term of the excess conormal sequence is `𝓕`. -/
theorem excessShortComplex_X₁ : (excessShortComplex i).X₁ = excessConormal i := rfl

/-- The middle term of the excess conormal sequence is `π^*𝒞_{Z/X}`. -/
def excessShortComplexX₂Iso :
    (excessShortComplex i).X₂ ≅
      (Scheme.Modules.pullback (exceptionalProj i).hom.left).obj (centreConormal i) :=
  Iso.refl _

/-- The last term of the excess conormal sequence is `𝒞_{E/X'}`. -/
theorem excessShortComplex_X₃ : (excessShortComplex i).X₃ = exceptionalConormal i := rfl

/-- **The excess conormal sequence is short exact.** -/
theorem excessShortComplex_shortExact : (excessShortComplex i).ShortExact where
  exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _)

/-! ### The conormal sheaf of the exceptional divisor and its ideal sheaf -/

open Stacks.Immersion Stacks.ClosedImmersion in
/-- **`𝒞_{E/X'} ≅ j^*ℐ_E`**: the conormal sheaf of the exceptional divisor is the restriction to
`E` of its ideal sheaf `ℐ_E = 𝒪_{X'}(-E)` (Tag 0B3P). -/
def exceptionalConormalIso :
    exceptionalConormal i ≅
      (Scheme.Modules.pullback (exceptionalHom i).hom.left).obj
        (idealSheaf (exceptionalHom i).hom.left.toLRSHom.toShHom) :=
  (conormalSheafSelfIso (exceptionalHom i).hom.left).symm

/-! ### Invertibility of the ideal of the exceptional divisor -/

/-- The pullback to the blowing up of the ideal of the centre is an effective Cartier divisor. -/
instance isEffectiveCartierDivisor_exceptionalIdeal :
    Stacks.Divisors.IsEffectiveCartierDivisor
      (i.hom.left.ker.comap (Stacks.Blowup.blowUpToBase i.hom.left.ker)) :=
  Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal_reesData _

open Stacks.ClosedImmersion in
/-- **The ideal sheaf `ℐ_E = 𝒪_{X'}(-E)` of the exceptional divisor is invertible**: `E` is the
closed subscheme cut out by the exceptional ideal (`exceptionalToSubscheme`), an effective Cartier
divisor (Tag 02OS). -/
@[sga "6 VII 3.1" "partial"]
theorem isInvertible_idealSheaf_exceptionalHom :
    Stacks.SheafOfModules.IsInvertible (blowupObj i).obj.left.presheaf
      (blowupObj i).obj.left.ringCatSheaf.2
      (idealSheaf (exceptionalHom i).hom.left.toLRSHom.toShHom) := by
  have h := @Stacks.Divisors.Eta.isInvertible_idealSheaf _ _
    (isEffectiveCartierDivisor_exceptionalIdeal i)
  exact @Stacks.SheafOfModules.isInvertible_of_iso _ _ _ _ _ _ _ _ _
    (Stacks.Conormal.AffineCotangent.SourceTransport.idealSheafIsoOfIsoSourceOfCompEq
      (asIso (exceptionalToSubscheme i))
      (i.hom.left.ker.comap (Stacks.Blowup.blowUpToBase i.hom.left.ker)).subschemeι
      (exceptionalHom i).hom.left (exceptionalToSubscheme_subschemeι i)).symm h

/-- **`𝒞_{E/X'}` is invertible**: it is `j^*ℐ_E`. -/
theorem isInvertible_exceptionalConormal :
    AlgebraicGeometry.SheafOfModules.IsInvertible (exceptionalObj i).obj.left.presheaf
      (exceptionalObj i).obj.left.ringCatSheaf.2 (exceptionalConormal i) := by
  have := isInvertible_idealSheaf_exceptionalHom i
  have : Stacks.SheafOfModules.IsInvertible (exceptionalObj i).obj.left.presheaf
      (exceptionalObj i).obj.left.ringCatSheaf.2
      ((Scheme.Modules.pullback (exceptionalHom i).hom.left).obj
        (Stacks.ClosedImmersion.idealSheaf (exceptionalHom i).hom.left.toLRSHom.toShHom)) :=
    Stacks.ProjectiveBundleQuotients.isInvertible_pullback_obj _ _
  exact Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
    (Stacks.SheafOfModules.isInvertible_of_iso _ _ (exceptionalConormalIso i).symm)

/-! ### Ranks -/

section Rank

variable {n e : ℕ} (hX : RelativeDimension X.obj.hom n) (hZ : RelativeDimension Z.obj.hom e)

include hX hZ in
/-- **`𝒞_{Z/X}` is finite locally free of rank `n - e`** for `X` and `Z` equidimensional of
dimensions `n` and `e`: by Tag 06AA the conormal sequence
`0 ⟶ 𝒞_{Z/X} ⟶ i^*Ω_{X/k} ⟶ Ω_{Z/k} ⟶ 0` is short exact, and `Ω_{X/k}`, `Ω_{Z/k}` are finite
locally free of ranks `n` and `e` (Tag 02G1). -/
theorem isFiniteLocallyFreeOfRank_centreConormal :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (centreConormal i)
      (n - e) := by
  have : Smooth (i.hom.left ≫ X.obj.hom) := by rw [Over.w i.hom]; infer_instance
  have hZ' : RelativeDimension (i.hom.left ≫ X.obj.hom) e := by
    have key : ∀ (q : Z.obj.left ⟶ Spec (.of k)) [LocallyOfFiniteType q], q = Z.obj.hom →
        RelativeDimension q e := by
      rintro q _ rfl; exact hZ
    exact key _ (Over.w i.hom)
  exact Stacks.ConormalSequenceRight.isFiniteLocallyFreeOfRank_conormalSheaf i.hom.left
    X.obj.hom hX hZ'

include hX hZ in
/-- **`𝓕` is finite locally free of rank `n - e - 1`** when `e < n`: it is the kernel of the
surjection `π^*𝒞_{Z/X} ⟶ 𝒞_{E/X'}` from a module of rank `n - e` onto an invertible one. -/
theorem isFiniteLocallyFreeOfRank_excessConormal (he : e < n) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (excessConormal i)
      (n - e - 1) := by
  have := isFiniteLocallyFreeOfRank_centreConormal i hX hZ
  have hM : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (exceptionalProj i).hom.left).obj (centreConormal i))
      (n - e - 1 + 1) := by
    rw [Nat.sub_add_cancel (by omega)]
    exact AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback _ _ _
  exact Stacks.ProjectiveBundleSplitting.isFiniteLocallyFreeOfRank_kernel_of_epi_isInvertible_pred
    (excessConormalMap i) inferInstance (isInvertible_exceptionalConormal i) _ hM

end Rank

end Stacks.WeilCohomology.SmoothProjectiveScheme

end
