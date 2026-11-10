module

public import StacksFrontier.AlgebraicGeometry.AmpleWire.UnitStalk
public import StacksFrontier.AlgebraicGeometry.FiniteSurjectiveCoherentSupport.Basic
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FiniteAlgebraAlgebraization
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.ProperSupport
public import StacksFrontier.AlgebraicGeometry.RelativeSpecEssSurj.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The support of a finite algebra sheaf is the image of its relative spectrum

Let `E` be a quasi-coherent sheaf of `𝒪_T`-algebras and `π : Spec_T(E) ⟶ T` its relative
spectrum. This file proves

* `SheafOfModules.supp (underlyingModule E) = Set.range π.base` when `E` is finite, and
* that properness of `π` over a further base is the same condition as properness of the support
  of `underlyingModule E` over that base.

The second statement is `AlgebraicGeometry.AlgebraSheafProperSupportBridge`, which identifies
the two readings of the properness clauses of Grothendieck existence: [Stacks, Tag 088F] states
them through the support of a coherent module, while
`AlgebraicGeometry.AdicFiniteAlgebraAlgebraization` states them through the relative spectrum.

## The support computation

[Stacks, Tag 01LX] (3) presents `E` as the direct image of the structure sheaf of its relative
spectrum: `Stacks.AffineAlgebraEquivalence.pushforwardAlgebraIso` is an isomorphism of algebra
sheaves `π_* 𝒪 ≅ E`, and the `𝒪_T`-module underlying a direct image of algebras is the direct
image of the underlying module on the nose. So the support of `underlyingModule E` is the
support of `π_* 𝒪_{Spec_T(E)}`, and the two inclusions are:

* off the image of `π` the direct image has no sections near the point, which is
  `Stacks.AlgebraicGeometry.FiniteSurjectiveCoherentSupport.supp_pushforward_subset` applied to
  the image itself, closed because a finite morphism is universally closed;
* on the image the stalk is nonzero, because the germ at `π z` of the unit section of
  `π_* 𝒪` maps, under `TopCat.Presheaf.stalkPushforward` followed by the identification of the
  stalk of `𝒪` read as a module with the stalk of `𝒪` read as a ring
  (`Stacks.Ample.unitStalkFun`), to `1` in the local ring at `z`.

## From the support to properness

Write `Z = range π.base`, a closed subset of `T` whose underlying set is the support. The
equivalence of `IsProper (π ≫ g)` with `IsProperOver g Z` is the two halves of
[Stacks, Tag 0CYQ] and [Stacks, Tag 0CYL]:

* `AlgebraicGeometry.isProperOver_closedImage` carries properness of all of `Spec_T(E)` over the
  base along the universally closed `π` to properness of the image;
* conversely, properness of *some* closed subscheme structure on `Z` over the base transfers to
  *every* one (`AlgebraicGeometry.exists_isProper_iff_forall_isProper`), in particular to the
  scheme-theoretic image `π.ker`, whose support is the closure of the range, i.e. the range,
  and `π` factors through it by a finite morphism, since `Scheme.Hom.imageι` is a closed
  immersion and finiteness cancels on the right against a separated morphism.

Neither half needs `g` to be separated: the image lemma used is the universally closed one, not
the separated one.

## Main results

* `AlgebraicGeometry.mem_supp_pushforward_unit`: the stalk of `p_* 𝒪_W` at a point of the image
  of `p` is nonzero.
* `AlgebraicGeometry.supp_underlyingModule_eq_range_relativeSpecToBase`: the support of the
  module underlying a finite quasi-coherent algebra sheaf is the image of its relative spectrum.
* `AlgebraicGeometry.isProper_relativeSpecToBase_comp_iff_hasProperSupport`: properness of the
  relative spectrum over a further base is properness of that support.
* `AlgebraicGeometry.algebraSheafProperSupportBridge`: the statement
  `AlgebraicGeometry.AlgebraSheafProperSupportBridge` holds.

## References

* [Stacks Project, Tag 01LX](https://stacks.math.columbia.edu/tag/01LX)
* [Stacks Project, Tag 0CYL](https://stacks.math.columbia.edu/tag/0CYL)
* [Stacks Project, Tag 0CYQ](https://stacks.math.columbia.edu/tag/0CYQ)
* [Stacks Project, Tag 0CYS](https://stacks.math.columbia.edu/tag/0CYS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.AffineAlgebraEquivalence
open Stacks.RelativeSpec (AlgebraSheaf)

universe u

namespace AlgebraicGeometry

open Stacks.Algebraization (HasProperSupport)

/-! ### The stalk of a direct image of a structure sheaf on the image -/

/-- The stalk of `p_* 𝒪_W` at a point of the image of `p` is nonzero. The germ there of the
unit section is carried by `TopCat.Presheaf.stalkPushforward`, followed by the identification of
the stalk of `𝒪_W` read as a module with the stalk of `𝒪_W` read as a ring, to `1` in the local
ring of `W` at the chosen preimage, and that is not `0`. -/
public theorem mem_supp_pushforward_unit {W T : Scheme.{u}} (p : W ⟶ T) (z : W) :
    p.base z ∈ SheafOfModules.supp
      ((Scheme.Modules.pushforward p).obj (Stacks.Ample.unitModule W)) := by
  have hz : z ∈ p ⁻¹ᵁ (⊤ : T.Opens) := trivial
  have hpush := TopCat.Presheaf.stalkPushforward_germ_apply Ab.{u} p.base
    (Stacks.Ample.unitModule W).val.presheaf (⊤ : T.Opens) z trivial
    (1 : Γ(W, p ⁻¹ᵁ (⊤ : T.Opens)))
  have hunit := Stacks.Ample.unitStalkFun_germ W z (p ⁻¹ᵁ (⊤ : T.Opens)) hz
    (1 : Γ(W, p ⁻¹ᵁ (⊤ : T.Opens)))
  have key := ((congrArg (Stacks.Ample.unitStalkFun W z) hpush).trans hunit).trans
    (map_one (W.presheaf.germ (p ⁻¹ᵁ (⊤ : T.Opens)) z hz).hom)
  refine ⟨(((Scheme.Modules.pushforward p).obj (Stacks.Ample.unitModule W)).presheaf.germ
    (⊤ : T.Opens) (p.base z) trivial).hom (1 : Γ(W, p ⁻¹ᵁ (⊤ : T.Opens))), fun hzero => ?_⟩
  erw [hzero] at key
  erw [map_zero, Stacks.Ample.unitStalkFun, map_zero] at key
  exact zero_ne_one key

/-! ### The support of a finite algebra sheaf -/

/-- The `𝒪_T`-module underlying a quasi-coherent algebra sheaf is the direct image of the
structure sheaf of its relative spectrum: this is [Stacks, Tag 01LX] (3)
(`Stacks.AffineAlgebraEquivalence.pushforwardAlgebraIso`) read on underlying modules. -/
public def underlyingModuleIsoPushforwardUnit {T : Scheme.{u}} (E : AlgebraSheaf T)
    [AlgebraSheaf.IsQuasicoherent E] :
    AlgebraSheaf.underlyingModule E ≅
      (Scheme.Modules.pushforward (relativeSpecToBase E)).obj
        (Stacks.Ample.unitModule (relativeSpec E)) :=
  (Stacks.RelativeSpec.AlgebraSheaf.underlyingModuleIso (pushforwardAlgebraIso E)).symm

/-- The support of the module underlying a finite quasi-coherent algebra sheaf is the image of
its relative spectrum. -/
@[sga "3 VIA 2.1.3" "special case"]
public theorem supp_underlyingModule_eq_range_relativeSpecToBase {T : Scheme.{u}}
    (E : AlgebraSheaf T) (hqc : AlgebraSheaf.IsQuasicoherent E)
    (hfin : AlgebraSheaf.IsFinite E) :
    SheafOfModules.supp (AlgebraSheaf.underlyingModule E) =
      Set.range (@relativeSpecToBase _ E hqc).base := by
  have := hqc
  have : IsFinite (relativeSpecToBase E) := isFinite_relativeSpecToBase E hfin
  rw [SheafOfModules.supp_eq_of_iso (underlyingModuleIsoPushforwardUnit E)]
  exact Set.Subset.antisymm
    (Stacks.AlgebraicGeometry.FiniteSurjectiveCoherentSupport.supp_pushforward_subset
      (relativeSpecToBase E) _ (relativeSpecToBase E).isClosedMap.isClosed_range subset_rfl)
    (Set.range_subset_iff.2 (mem_supp_pushforward_unit (relativeSpecToBase E)))

/-! ### The bridge -/

/-- If `p` is finite and `p ≫ g` is proper, then the image of `p` is proper over the base. -/
private theorem isProperOver_range_of_isProper_comp {X T S : Scheme.{u}} (p : X ⟶ T) [IsFinite p]
    (g : T ⟶ S) [LocallyOfFiniteType g] [IsProper (p ≫ g)] :
    IsProperOver g ⟨Set.range p.base, p.isClosedMap.isClosed_range⟩ := by
  have htop : IsProperOver (p ≫ g) (⊤ : Closeds X) := by
    change IsProper ((Scheme.IdealSheafData.vanishingIdeal (⊤ : Closeds X)).subschemeι ≫ (p ≫ g))
    infer_instance
  have heq : p.closedImage ⊤ = ⟨Set.range p.base, p.isClosedMap.isClosed_range⟩ := by
    refine Closeds.ext ?_
    change p.base '' Set.univ = Set.range p.base
    exact Set.image_univ
  exact heq ▸ isProperOver_closedImage p g ⊤ htop

/-- If `p` is finite and the image of `p` is proper over the base, then `p ≫ g` is proper. -/
private theorem isProper_comp_of_isProperOver_range {X T S : Scheme.{u}} (p : X ⟶ T) [IsFinite p]
    (g : T ⟶ S) [LocallyOfFiniteType g]
    (h : IsProperOver g ⟨Set.range p.base, p.isClosedMap.isClosed_range⟩) :
    IsProper (p ≫ g) := by
  have hker : p.ker.support = ⟨Set.range p.base, p.isClosedMap.isClosed_range⟩ := by
    refine Closeds.ext ?_
    rw [Scheme.Hom.support_ker]
    exact p.isClosedMap.isClosed_range.closure_eq
  have : IsProper (p.ker.subschemeι ≫ g) :=
    (exists_isProper_iff_forall_isProper g _).1
      ((isProperOver_iff_exists_isProper g _).1 h) _ hker
  have : IsFinite p.toImage := by
    have : IsFinite (p.toImage ≫ p.imageι) := by
      rw [Scheme.Hom.toImage_imageι]
      infer_instance
    exact IsFinite.of_comp _ p.imageι
  have hcomp : IsProper (p.toImage ≫ (p.imageι ≫ g)) := inferInstance
  rwa [← Category.assoc, Scheme.Hom.toImage_imageι] at hcomp

/-- For a finite quasi-coherent algebra sheaf, properness of the relative spectrum over a further
base and properness of the support of the underlying module over that base are the same
condition. -/
public theorem isProper_relativeSpecToBase_comp_iff_hasProperSupport {T S : Scheme.{u}}
    (g : T ⟶ S) [LocallyOfFiniteType g] (E : AlgebraSheaf T)
    (hqc : AlgebraSheaf.IsQuasicoherent E) (hfin : AlgebraSheaf.IsFinite E) :
    IsProper (@relativeSpecToBase _ E hqc ≫ g) ↔
      HasProperSupport g (AlgebraSheaf.underlyingModule E) := by
  have := hqc
  have : IsFinite (relativeSpecToBase E) := isFinite_relativeSpecToBase E hfin
  have hsupp : ((⟨Set.range (relativeSpecToBase E).base,
      (relativeSpecToBase E).isClosedMap.isClosed_range⟩ : Closeds T) : Set T) =
      SheafOfModules.supp (AlgebraSheaf.underlyingModule E) :=
    (supp_underlyingModule_eq_range_relativeSpecToBase E hqc hfin).symm
  refine ⟨fun _ => ⟨_, hsupp, isProperOver_range_of_isProper_comp _ g⟩, fun ⟨Z', hZ', hp'⟩ => ?_⟩
  exact isProper_comp_of_isProperOver_range _ g
    ((Closeds.ext (hZ'.trans hsupp.symm) : Z' = _) ▸ hp')

/-- For a finite quasi-coherent algebra sheaf, properness of the relative spectrum over a base is
properness of the support of the underlying module:
`AlgebraicGeometry.AlgebraSheafProperSupportBridge` holds. -/
public theorem algebraSheafProperSupportBridge : AlgebraSheafProperSupportBridge.{u} := by
  intro T S g _ E hqc hfin
  exact isProper_relativeSpecToBase_comp_iff_hasProperSupport g E hqc hfin

end AlgebraicGeometry

end
