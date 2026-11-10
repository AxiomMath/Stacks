module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.Scheme.IdealSheafEqToHom
public import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The closure of a closed subscheme of an open subscheme

Let `j : U ⟶ X` be an open immersion and let `I` be an ideal sheaf on `U`, cutting out a closed
subscheme of `U`.  The *closure* of that closed subscheme in `X` is the reduced induced closed
subscheme structure on the topological closure of the image of the support of `I`.  It is the
smallest closed subscheme of `X` whose intersection with `U` contains the given one, and it is
the geometric device by which data on an open subscheme is extended to the ambient scheme.

## Main definitions

* `Stacks.IdealSheaf.closureIdeal`: the ideal sheaf on `X` cutting out the closure.
* `Stacks.IdealSheaf.closureSubschemeOpenMap`: the comparison morphism from the closed
  subscheme of `U` cut out by `I` to the closure, an open immersion identifying the former with
  the part of the closure lying over `U`.
* `Stacks.IdealSheaf.closureSubschemeOpenIso`: the identification exhibiting the square formed
  by the two closed subschemes, the open immersion and the comparison morphism as cartesian.

## Main results

* `Stacks.IdealSheaf.closureIdeal_comap`: taking the closure and then intersecting with `U`
  recovers the original closed subscheme, provided it is reduced.  This is the key geometric
  fact: the closure is an extension of the given closed subscheme, not merely of its support.
* `Stacks.IdealSheaf.closureIdeal_integral`: the closure of an integral closed subscheme is
  integral.
* `Stacks.IdealSheaf.closureIdeal_family_isLocallyFinite`: closures of a locally finite family
  of closed subschemes of `U` form a locally finite family in `X`, when `X` is locally
  Noetherian.
* `Stacks.IdealSheaf.closureSubschemeOpenMap_comp_subschemeι`: the comparison square commutes.
* `Stacks.IdealSheaf.open_comap_vanishingIdeal_eq`: the closure of the integral closed
  subscheme with generic point `x` meets `U` in the integral closed subscheme with generic
  point `x`.

## Implementation notes

Reducedness, rather than integrality, is what makes `closureIdeal_comap` work: both sides of
the asserted equality have the same support, both are reduced, and a closed subset carries only
one reduced closed subscheme structure
(`Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme`).  The supports agree because `j`
is an open immersion, so its underlying map is an injective open map and therefore commutes
with closures both ways.

Local finiteness uses that an open immersion into a locally Noetherian scheme is quasi-compact,
so that the preimage of an affine open `V` of `X` is a compact subset `K` of `U`; the closure of
the image of the support of `I` meets `V` exactly when the support of `I` meets `K`, because `V`
is open.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.IdealSheaf

/-! ### The closure of a closed subscheme of an open subscheme -/

/-- The closure in `X` of the closed subscheme of `U` cut out by `I`, along a morphism
`j : U ⟶ X`: the reduced induced closed subscheme structure on the topological closure of the
image of the support of `I`. -/
noncomputable def closureIdeal {U X : Scheme.{u}} (j : U ⟶ X) (I : U.IdealSheafData) :
    X.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal (Closeds.closure (j.base '' (I.support : Set U)))

/-- The closure is supported on the topological closure of the image of the support. -/
theorem closureIdeal_support {U X : Scheme.{u}} (j : U ⟶ X) (I : U.IdealSheafData) :
    (closureIdeal j I).support = Closeds.closure (j.base '' (I.support : Set U)) := rfl

/-- Closures along an open immersion into a locally Noetherian scheme of a locally finite family
of closed subschemes of the open subscheme form a locally finite family. -/
theorem closureIdeal_family_isLocallyFinite {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    [IsLocallyNoetherian X] {ι : Type*} (I : ι → U.IdealSheafData)
    (hI : LocallyFinite fun n ↦ ((I n).support : Set U)) :
    LocallyFinite fun n ↦ ((closureIdeal j (I n)).support : Set X) := by
  intro x
  obtain ⟨_, ⟨V, hVaff, rfl⟩, hxV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hKcompact : IsCompact (j.base ⁻¹' (V : Set X)) := j.isCompact_preimage hVaff.isCompact
  refine ⟨V, V.2.mem_nhds hxV, (hI.finite_nonempty_inter_compact hKcompact).subset
    fun n hn ↦ ?_⟩
  obtain ⟨y, hyclose, hyV⟩ :
      (((closureIdeal j (I n)).support : Set X) ∩ (V : Set X)).Nonempty := hn
  rw [closureIdeal_support] at hyclose
  obtain ⟨v, hvV, w, hwI, hvw⟩ := mem_closure_iff.mp (Closeds.mem_closure.1 hyclose) V V.2 hyV
  exact ⟨w, hwI, show j.base w ∈ (V : Set X) from hvw ▸ hvV⟩

/-- The closure of an integral closed subscheme along an open immersion is integral: its
support is the closure of a continuous image of an irreducible set, hence irreducible, and the
reduced induced structure is reduced. -/
theorem closureIdeal_integral {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (I : U.IdealSheafData) [IsIntegral I.subscheme] :
    IsIntegral (closureIdeal j I).subscheme := by
  have hIrrI : IsIrreducible (I.support : Set U) := by
    rw [← I.range_subschemeι, ← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ I.subscheme).image _
      I.subschemeι.continuous.continuousOn
  have : IsReduced (closureIdeal j I).subscheme :=
    Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _
  have : IrreducibleSpace (closureIdeal j I).subscheme :=
    Scheme.IdealSheafData.irreducibleSpace_subscheme X (closureIdeal j I) (by
      rw [Scheme.IdealSheafData.range_subschemeι, closureIdeal_support]
      exact (hIrrI.image j.base j.continuous.continuousOn).closure)
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- **The closure is an extension.** Intersecting the closure of a reduced closed subscheme of
an open subscheme with that open subscheme returns the subscheme one started with. -/
theorem closureIdeal_comap {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (I : U.IdealSheafData) [IsReduced I.subscheme] : (closureIdeal j I).comap j = I := by
  have hsupp : ((closureIdeal j I).comap j).support = I.support := by
    rw [Scheme.IdealSheafData.support_comap, closureIdeal_support]
    ext x
    change x ∈ j.base ⁻¹' (closure (j.base '' (I.support : Set U)) : Set X) ↔ x ∈ I.support
    rw [j.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage j.continuous,
      Set.preimage_image_eq _ j.isOpenEmbedding.injective, I.support.isClosed.closure_eq]
    rfl
  have : IsReduced (closureIdeal j I).subscheme :=
    Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _
  have : IsReduced ((closureIdeal j I).comap j).subscheme :=
    isReduced_of_isOpenImmersion
      (((closureIdeal j I).comapIso j).hom ≫ pullback.snd j (closureIdeal j I).subschemeι)
  rw [Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme
      ((closureIdeal j I).comap j) I.support hsupp,
    ← Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme I I.support rfl]

/-! ### The comparison morphism to the closure -/

/-- **The comparison square is cartesian.** The closed subscheme of `U` cut out by a reduced
ideal sheaf `I` is the fibre product of `j` with the closed immersion of the closure of `I`. -/
@[ega "I 5.2.3"]
noncomputable def closureSubschemeOpenIso {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (I : U.IdealSheafData) [IsReduced I.subscheme] :
    I.subscheme ≅ pullback j (closureIdeal j I).subschemeι :=
  eqToIso (congrArg Scheme.IdealSheafData.subscheme (closureIdeal_comap j I)).symm ≪≫
    (closureIdeal j I).comapIso j

/-- The cartesian identification of a closed subscheme of an open subscheme with the fibre
product is compatible with the projection to the open subscheme. -/
private theorem closureIso_hom_fst_comp {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (I : U.IdealSheafData) [IsReduced I.subscheme] :
    (closureSubschemeOpenIso j I).hom ≫ pullback.fst j (closureIdeal j I).subschemeι =
      I.subschemeι := by
  dsimp only [closureSubschemeOpenIso, Iso.trans_hom, eqToIso.hom]
  rw [Category.assoc, Scheme.IdealSheafData.comapIso_hom_fst]
  exact eqToHom_subscheme_comp_subschemeι I ((closureIdeal j I).comap j)
    (closureIdeal_comap j I).symm

/-- The comparison morphism from a reduced closed subscheme of an open subscheme to its closure
in the ambient scheme. -/
noncomputable def closureSubschemeOpenMap {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (I : U.IdealSheafData) [IsReduced I.subscheme] :
    I.subscheme ⟶ (closureIdeal j I).subscheme :=
  (closureSubschemeOpenIso j I).hom ≫ pullback.snd j (closureIdeal j I).subschemeι

/-- The comparison morphism to the closure is an open immersion: it is the base change of the
open immersion `j` along the closed immersion of the closure. -/
instance closureSubschemeOpenMap_isOpenImmersion {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (I : U.IdealSheafData) [IsReduced I.subscheme] :
    IsOpenImmersion (closureSubschemeOpenMap j I) := by
  have : IsOpenImmersion (pullback.snd j (closureIdeal j I).subschemeι) :=
    MorphismProperty.of_isPullback
      (IsPullback.of_hasPullback j (closureIdeal j I).subschemeι) inferInstance
  exact IsOpenImmersion.comp _ _

/-- The comparison square commutes: the closed immersion of a closed subscheme of an open
subscheme, followed by the open immersion, is the comparison morphism followed by the closed
immersion of the closure. -/
theorem closureSubschemeOpenMap_comp_subschemeι {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (I : U.IdealSheafData) [IsReduced I.subscheme] :
    closureSubschemeOpenMap j I ≫ (closureIdeal j I).subschemeι = I.subschemeι ≫ j := by
  rw [closureSubschemeOpenMap, Category.assoc, ← pullback.condition, ← Category.assoc,
    closureIso_hom_fst_comp]

/-- The cartesian identification of a closed subscheme of an open subscheme with the fibre
product is compatible with the projection to the open subscheme. -/
theorem closureSubschemeOpenIso_hom_fst {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (I : U.IdealSheafData) [IsReduced I.subscheme] :
    (closureSubschemeOpenIso j I).hom ≫ pullback.fst j (closureIdeal j I).subschemeι =
      I.subschemeι :=
  closureIso_hom_fst_comp j I

/-- The closure of the integral closed subscheme of an open subscheme with generic point `x`
meets that open subscheme in the integral closed subscheme with generic point `x`. -/
theorem open_comap_vanishingIdeal_eq {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (x : U) :
    (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({j.base x} : Set X))).comap j =
      Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set U)) := by
  have : IsReduced
      (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set U))).subscheme :=
    Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _
  convert closureIdeal_comap j
    (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set U))) using 1
  unfold closureIdeal
  congr 2
  apply SetLike.coe_injective
  change closure ({j.base x} : Set X) = closure (j.base '' closure ({x} : Set U))
  rw [closure_image_closure j.continuous]
  simp

end Stacks.IdealSheaf

end
