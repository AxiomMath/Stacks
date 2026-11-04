module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import StacksFrontier.AlgebraicGeometry.Cohomology.AffineCoverVanishing.SeparatedCover
public import StacksFrontier.AlgebraicGeometry.HigherDirectImage.RightDerivedPlus
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedAmplitude.UpperBounds
public import StacksFrontier.AlgebraicGeometry.Perfect.QuasiCoherentDerived.DirectSums
public import StacksFrontier.AlgebraicGeometry.RingedSpace.DerivedPushforward
public import StacksFrontier.Topology.Sheaves.Cohomology.CechToCohomology.AcyclicCovering
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ConnectivityOnABasis
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.SectionsOverAnOpen
import StacksCore.Tactic.StacksAttribute

/-!
# A uniform vanishing degree for the unbounded derived direct image

Let `f : X ⟶ S` be a quasi-compact and quasi-separated morphism of schemes with `S`
quasi-compact. There is an integer `N`, depending on `f` alone, such that every object `E` of
`D_QCoh(𝒪_X)` living in degrees `≤ 0` has `H^m(Rf_*E) = 0` for `m ≥ N`.

## Main results

* `AlgebraicGeometry.exists_isZero_hgroup_preimage_isBasis` — a basis of affine opens of `S` and
  one degree above which the cohomology of every quasi-coherent `𝒪_X`-module over the inverse
  image of a basis member vanishes.
* `AlgebraicGeometry.exists_isZero_homology_derivedPushforward_of_isLE` — **[Stacks, Tag 08D5]
  part (2)**: a uniform degree above which the cohomology sheaves of `Rf_*E` vanish.

## Implementation notes

The source deduces the uniform vanishing of `H^p(f⁻¹V, ℱ)` over the affine opens `V ⊆ S` from
[Stacks, Tag 01XJ] and [Stacks, Tag 01XK]: the sheaf `R^pf_*ℱ` vanishes identically for `p ≥ N`,
and over an affine `V` the module `H^p(f⁻¹V, ℱ)` is its module of sections. That route compares
the cohomology of a module over an open `U ⊆ X` with the cohomology of its restriction to `U`
as an open subscheme. Here the bound is instead read off directly from [Stacks, Tag 071L], the
estimate that is also the engine of Tag 01XJ: a finite affine cover `S = ⋃_j S_j` and finite
affine covers `f⁻¹(S_j) = ⋃_i U_{ji}` are chosen once, and for an affine `V ⊆ S_j` the opens
`U_{ji} ⊓ f⁻¹V` are again affine, so the Mayer--Vietoris estimate over `f⁻¹V` is bounded by the
one over `f⁻¹(S_j)`.

Affineness of `U_{ji} ⊓ f⁻¹V` is `AlgebraicGeometry.IsAffineOpen.inf_preimage`: the morphism
from the affine `U_{ji}` to the affine `S_j` is an affine morphism, so the inverse image of the
affine open `V ⊆ S_j` under it is affine. This is where it matters that the basis consists of
affine opens *contained in a member of the chosen cover of* `S`, rather than of all affine opens
of `S`; the latter is also a basis but the argument does not apply to it.

The Mayer--Vietoris induction over the subsets of the index set of the cover is
`Stacks.Cohomology.AffineCover.isZero_cohomologyPresheaf_of_finset_separated_cover`. It takes the
quasi-compactness of the intersections as a hypothesis instead of asking the ambient space to be
quasi-separated, which is what makes it applicable here: `S` is only assumed quasi-compact, so `X`
need not be a quasi-separated space, while each `f⁻¹(S_j)` is. Quasi-compactness is supplied by
`AlgebraicGeometry.isCompact_inf_finsetInf`.

The transport from the cohomology groups of [Stacks, Tag 071L] to the bounded-below right
derived functors of the sections functor that Tag 08D4 consumes runs through two exact and
faithful functors — the forgetful functor to abelian groups and restriction of scalars — and is
`AlgebraicGeometry.isZero_rightDerivedPlus_preimageSections_of_isZero_hgroup'`.

## References

* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
* [Stacks Project, Tag 08D4](https://stacks.math.columbia.edu/tag/08D4)
* [Stacks Project, Tag 071L](https://stacks.math.columbia.edu/tag/071L)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
* [Stacks Project, Tag 0D66](https://stacks.math.columbia.edu/tag/0D66)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.AffineCover

namespace AlgebraicGeometry

universe u

variable {X S : Scheme.{u}}

/-! ### Affine opens of the source over an affine open of the target -/

/-- **An affine open of the source meets the inverse image of an affine open of the target in an
affine open.** Let `W ⊆ X` be an affine open lying over an affine open `B ⊆ S`, and let `V ⊆ B` be
an affine open. Then `W ⊓ f⁻¹V` is affine.

The morphism `W ⟶ B` induced by `f` is a morphism of affine schemes, hence an affine morphism, so
the inverse image in `W` of the affine open `V ⊆ B` is affine; its image under the open immersion
`W ⟶ X` is `W ⊓ f⁻¹V`. -/
theorem IsAffineOpen.inf_preimage (f : X ⟶ S) {W : X.Opens} (hW : IsAffineOpen W)
    {B V : S.Opens} (hB : IsAffineOpen B) (hV : IsAffineOpen V)
    (hWB : W ≤ f ⁻¹ᵁ B) (hVB : V ≤ B) : IsAffineOpen (W ⊓ f ⁻¹ᵁ V) := by
  have : IsAffine (W : Scheme) := hW
  have : IsAffine (B : Scheme) := hB
  have hrange : Set.range (W.ι ≫ f).base ⊆ Set.range B.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro y ⟨x, rfl⟩
    exact hWB x.2
  let l : (W : Scheme) ⟶ (B : Scheme) := IsOpenImmersion.lift B.ι (W.ι ≫ f) hrange
  have hfac : l ≫ B.ι = W.ι ≫ f := IsOpenImmersion.lift_fac _ _ _
  have hV' : IsAffineOpen (B.ι ⁻¹ᵁ V) :=
    hV.preimage_of_isOpenImmersion B.ι (by rw [Scheme.Opens.opensRange_ι]; exact hVB)
  have hpre : IsAffineOpen (l ⁻¹ᵁ (B.ι ⁻¹ᵁ V)) := IsAffineHom.isAffine_preimage _ hV'
  rw [show l ⁻¹ᵁ (B.ι ⁻¹ᵁ V) = W.ι ⁻¹ᵁ (f ⁻¹ᵁ V) by
    rw [← Scheme.Hom.comp_preimage, hfac, Scheme.Hom.comp_preimage]] at hpre
  have himg := hpre.image_of_isOpenImmersion W.ι
  rwa [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι] at himg

/-! ### Compactness and covering numbers inside a quasi-separated open -/

/-- A finite intersection of opens that meet a quasi-compact quasi-separated open `Y ⊆ X` in
affine opens again meets `Y` in a quasi-compact open: the intersection may be computed inside `Y`,
where it is a finite intersection of quasi-compact opens. -/
theorem isCompact_inf_finsetInf (Y : X.Opens) [CompactSpace (Y : Scheme)]
    [QuasiSeparatedSpace (Y : Scheme)] {ι : Type*} (U : ι → X.Opens)
    (hU : ∀ i, IsAffineOpen (Y ⊓ U i)) (J : Finset ι) :
    IsCompact ((Y ⊓ J.inf U : X.Opens) : Set X) := by
  classical
  have hUc : ∀ i, IsCompact ((Y.ι ⁻¹ᵁ U i : (Y : Scheme).Opens) : Set (Y : Scheme)) := by
    intro i
    have h := ((hU i).preimage_of_isOpenImmersion Y.ι
      (by rw [Scheme.Opens.opensRange_ι]; exact inf_le_left)).isCompact
    rwa [Scheme.Hom.preimage_inf, Scheme.Opens.ι_preimage_self, top_inf_eq] at h
  have hinf : ∀ K : Finset ι,
      IsCompact ((K.inf fun i ↦ Y.ι ⁻¹ᵁ U i : (Y : Scheme).Opens) : Set (Y : Scheme)) := by
    intro K
    induction K using Finset.induction_on with
    | empty =>
      simpa using (CompactSpace.isCompact_univ : IsCompact (Set.univ : Set (Y : Scheme)))
    | @insert a K _ ih =>
      simpa [Finset.inf_insert] using QuasiSeparatedSpace.inter_isCompact
        ((Y.ι ⁻¹ᵁ U a : (Y : Scheme).Opens) : Set (Y : Scheme))
        ((K.inf fun i ↦ Y.ι ⁻¹ᵁ U i : (Y : Scheme).Opens) : Set (Y : Scheme))
        (Y.ι ⁻¹ᵁ U a).2 (hUc a) (K.inf fun i ↦ Y.ι ⁻¹ᵁ U i).2 ih
  have hpre : ∀ K : Finset ι, Y.ι ⁻¹ᵁ K.inf U = K.inf fun i ↦ Y.ι ⁻¹ᵁ U i := by
    intro K
    induction K using Finset.induction_on with
    | empty => simp
    | @insert a K _ ih => simp [Finset.inf_insert, Scheme.Hom.preimage_inf, ih]
  have himage : Y.ι ''ᵁ (Y.ι ⁻¹ᵁ J.inf U) = Y ⊓ J.inf U := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  rw [← himage]
  exact ((hpre J) ▸ hinf J).image Y.ι.continuous

/-- **Intersecting with a smaller open does not raise the affine covering number**, provided every
affine open of the larger one meets the smaller one in an affine open. -/
theorem minimalAffineCoverCardinality_inf_le {T Y Q : X.Opens} (hTY : T ≤ Y)
    (hQ : IsCompact ((Y ⊓ Q : X.Opens) : Set X))
    (haff : ∀ A : X.Opens, IsAffineOpen A → A ≤ Y → IsAffineOpen (A ⊓ T)) :
    minimalAffineCoverCardinality (T ⊓ Q) ≤ minimalAffineCoverCardinality (Y ⊓ Q) := by
  obtain ⟨A, hA, hAcover⟩ := exists_affine_cover_card_eq (Y ⊓ Q) hQ
  refine Nat.sInf_le ⟨fun k ↦ A k ⊓ T, fun k ↦ haff _ (hA k) ?_, ?_⟩
  · exact (hAcover ▸ le_iSup A k).trans inf_le_left
  · rw [show (⨆ k, A k ⊓ T) = (Y ⊓ Q) ⊓ T by rw [← iSup_inf_eq, hAcover]]
    exact le_antisymm (le_inf inf_le_right (inf_le_left.trans inf_le_right))
      (le_inf (le_inf (inf_le_left.trans hTY) inf_le_right) inf_le_left)

/-! ### The uniform vanishing degree over the inverse images of a basis -/

/-- **A uniform vanishing degree for the cohomology over the inverse images of a basis of the
target.** For a quasi-compact and quasi-separated morphism `f : X ⟶ S` with `S` quasi-compact
there are a basis `ℬ` of the topology of `S` consisting of affine opens and an integer `N` such
that `H^p(f⁻¹V, ℱ) = 0` for every `V ∈ ℬ`, every quasi-coherent `𝒪_X`-module `ℱ` and every
`p ≥ N`.

This is the content of [Stacks, Tag 01XJ] that [Stacks, Tag 08D5] consumes. Choose a finite
affine cover `S = ⋃_j S_j` and finite affine covers `f⁻¹(S_j) = ⋃_i U_{ji}`; take `ℬ` to be the
affine opens contained in some `S_j` and `N` the maximum over `j` and over subsets `J` of the
fibre index set of `|J| + t(f⁻¹(S_j) ⊓ ⋂_{i ∈ J} U_{ji})`, where `t` is the affine covering
number. For `V ∈ ℬ` contained in `S_j` the opens `A ⊓ f⁻¹V` are affine for every affine
`A ≤ f⁻¹(S_j)`, so intersecting with `f⁻¹V` does not raise any of those covering numbers, and the
Mayer--Vietoris estimate of [Stacks, Tag 071L] over `f⁻¹V` with the cover `U_{ji}` gives the
bound. -/
theorem exists_isZero_hgroup_preimage_isBasis (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    [CompactSpace S] :
    ∃ (ℬ : Set S.Opens) (N : ℕ), Opens.IsBasis ℬ ∧ (∀ V ∈ ℬ, IsAffineOpen V) ∧
      ∀ V ∈ ℬ, ∀ M : X.Modules, M.IsQuasicoherent → ∀ p : ℕ, N ≤ p →
        IsZero (Hgroup X.ringCatSheaf (f ⁻¹ᵁ V) p M) := by
  classical
  have htop : IsCompact ((⊤ : S.Opens) : Set S) := by
    simpa using (isCompact_univ : IsCompact (Set.univ : Set S))
  obtain ⟨m, Bo, hBo, hBocover⟩ := exists_fin_affine_cover_of_isCompact (⊤ : S.Opens) htop
  choose n Uo hUo hUocover using fun j : Fin m ↦
    exists_fin_affine_cover_of_isCompact (f ⁻¹ᵁ Bo j) (f.isCompact_preimage (hBo j).isCompact)
  refine ⟨{V : S.Opens | IsAffineOpen V ∧ ∃ j, V ≤ Bo j},
    Finset.univ.sup fun j : Fin m ↦ Finset.univ.sup fun J : Finset (Fin (n j)) ↦
      J.card + minimalAffineCoverCardinality ((f ⁻¹ᵁ Bo j) ⊓ J.inf (Uo j)),
    ?_, fun V hV ↦ hV.1, ?_⟩
  · refine Opens.isBasis_iff_nbhd.mpr fun {W x} hxW ↦ ?_
    obtain ⟨j, hxj⟩ : ∃ j, x ∈ Bo j := by
      have hx : x ∈ iSup Bo := by rw [hBocover]; trivial
      simpa using hx
    obtain ⟨V, hVmem, hxV, hVle⟩ :=
      Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens (U := W ⊓ Bo j) (x := x) ⟨hxW, hxj⟩
    exact ⟨V, ⟨hVmem, j, hVle.trans inf_le_right⟩, hxV, hVle.trans inf_le_left⟩
  · rintro V ⟨hVaff, j, hVB⟩ M hM p hp
    have : M.IsQuasicoherent := hM
    have hfin : ∀ B : S.Opens, IsAffineOpen B →
        CompactSpace ((f ⁻¹ᵁ B : X.Opens) : Scheme) ∧
          QuasiSeparatedSpace ((f ⁻¹ᵁ B : X.Opens) : Scheme) := fun B hB ↦ by
      have : IsAffine (B : Scheme) := hB
      have : CompactSpace (B : Scheme) := Scheme.compactSpace_of_isAffine _
      exact ⟨QuasiCompact.compactSpace_of_compactSpace (f ∣_ B),
        quasiSeparatedSpace_of_quasiSeparated (f ∣_ B)⟩
    obtain ⟨_, _⟩ := hfin V hVaff
    obtain ⟨_, _⟩ := hfin _ (hBo j)
    have hVpre : (f ⁻¹ᵁ V : X.Opens) ≤ f ⁻¹ᵁ Bo j := fun x hx ↦ hVB hx
    have hUle : ∀ i, Uo j i ≤ f ⁻¹ᵁ Bo j := fun i ↦ (hUocover j) ▸ le_iSup (Uo j) i
    have haffV : ∀ i, IsAffineOpen ((f ⁻¹ᵁ V : X.Opens) ⊓ Uo j i) := by
      intro i
      rw [inf_comm]
      exact IsAffineOpen.inf_preimage f (hUo j i) (hBo j) hVaff (hUle i) hVB
    have haffB : ∀ i, IsAffineOpen ((f ⁻¹ᵁ Bo j : X.Opens) ⊓ Uo j i) := by
      intro i
      rw [inf_eq_right.mpr (hUle i)]
      exact hUo j i
    refine (isZero_hgroup_iff_isZero_cohomologyPresheaf _ M p).mpr ?_
    rw [show (f ⁻¹ᵁ V : X.Opens) = (f ⁻¹ᵁ V : X.Opens) ⊓ Finset.univ.sup (Uo j) by
      rw [Finset.sup_univ_eq_iSup, hUocover j, inf_eq_left.mpr hVpre]]
    refine isZero_cohomologyPresheaf_of_finset_separated_cover (Uo j)
      (fun i ↦ have : IsAffine (Uo j i : Scheme) := hUo j i; inferInstance) M (f ⁻¹ᵁ V)
      Finset.univ _ (fun J ↦ isCompact_inf_finsetInf _ (Uo j) haffV J) (fun J _ ↦ ?_) p hp
    have hmon : minimalAffineCoverCardinality ((f ⁻¹ᵁ V : X.Opens) ⊓ J.inf (Uo j)) ≤
        minimalAffineCoverCardinality ((f ⁻¹ᵁ Bo j : X.Opens) ⊓ J.inf (Uo j)) :=
      minimalAffineCoverCardinality_inf_le hVpre
        (isCompact_inf_finsetInf _ (Uo j) haffB J)
        fun A hA hAle ↦ IsAffineOpen.inf_preimage f hA (hBo j) hVaff hAle hVB
    have hle : J.card + minimalAffineCoverCardinality
        ((f ⁻¹ᵁ Bo j : X.Opens) ⊓ J.inf (Uo j)) ≤
        Finset.univ.sup fun j' : Fin m ↦ Finset.univ.sup fun K : Finset (Fin (n j')) ↦
          K.card + minimalAffineCoverCardinality ((f ⁻¹ᵁ Bo j') ⊓ K.inf (Uo j')) :=
      le_trans (Finset.le_sup (f := fun K : Finset (Fin (n j)) ↦
        K.card + minimalAffineCoverCardinality ((f ⁻¹ᵁ Bo j) ⊓ K.inf (Uo j)))
        (Finset.mem_univ J)) (Finset.le_sup (f := fun j' : Fin m ↦
          Finset.univ.sup fun K : Finset (Fin (n j')) ↦
            K.card + minimalAffineCoverCardinality ((f ⁻¹ᵁ Bo j') ⊓ K.inf (Uo j')))
          (Finset.mem_univ j))
    omega

/-! ### From cohomology groups to the right derived functors of sections -/

section Sections

open Stacks.Cohomology.DerivedSectionsLeray
  (sectionsOverOpen preimageSections derivedPreimageSections derivedPreimageSectionsUnit)

attribute [local instance] HasDerivedCategory.standard

/-- Vanishing is reflected by a faithful additive functor: it carries the identity of the object
to zero, and an additive functor carries zero to zero. -/
theorem isZero_of_isZero_map {A B : Type*} [Category* A] [Category* B] [Preadditive A]
    [Preadditive B] (P : A ⥤ B) [P.Additive] [P.Faithful] {Z : A} (h : IsZero (P.obj Z)) :
    IsZero Z := by
  rw [IsZero.iff_id_eq_zero]
  refine P.map_injective ?_
  rw [P.map_id, P.map_zero]
  exact (IsZero.iff_id_eq_zero _).mp h

/-- **Restriction of scalars along a ring homomorphism preserves limits of any shape for which
they exist.** A limit of modules is computed on the underlying abelian groups, which restriction
of scalars leaves unchanged, and the forgetful functor to abelian groups reflects limits because
it preserves them and reflects isomorphisms.

Mathlib has restriction of scalars as a right adjoint only for commutative rings, where
extension of scalars is available; the rings of sections of a sheaf of rings carry no
commutativity. -/
theorem preservesLimitsOfShape_restrictScalars {R R' : Type u} [Ring R] [Ring R']
    (φ : R →+* R') {J : Type} [SmallCategory J] [HasLimitsOfShape J (ModuleCat.{u} R')]
    [HasLimitsOfShape J (ModuleCat.{u} R)] :
    PreservesLimitsOfShape J (ModuleCat.restrictScalars.{u} φ) :=
  have : PreservesLimitsOfShape J (ModuleCat.restrictScalars.{u} φ ⋙
      forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) :=
    inferInstanceAs (PreservesLimitsOfShape J (forget₂ (ModuleCat.{u} R') AddCommGrpCat.{u}))
  have : ReflectsLimitsOfShape J (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) :=
    reflectsLimitsOfShape_of_reflectsIsomorphisms
  preservesLimitsOfShape_of_reflects_of_preserves (ModuleCat.restrictScalars.{u} φ)
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})

variable (f : X ⟶ S) (V : S.Opens)

/-- **Sections over the inverse image of an open of the target**, as a module over `Γ(V, 𝒪_S)`,
read as a functor out of `AlgebraicGeometry.Scheme.Modules`.

This is `Stacks.Cohomology.DerivedSectionsLeray.preimageSections` of the underlying morphism of
ringed spaces; the type ascription is the crossing between the two interchangeable spellings of
the category of `𝒪_X`-modules. -/
abbrev preimageSectionsOver :
    X.Modules ⥤
      ModuleCat.{u} ((structureSheafRing S.toLocallyRingedSpace.toRingedSpace).obj.obj (op V)) :=
  preimageSections f.toLRSHom.toShHom V

/-- Sections over the inverse image of an open form an additive functor: addition of sections of
a sheaf of modules is computed open by open. -/
instance preimageSectionsOver_additive : (preimageSectionsOver f V).Additive where
  map_add := rfl

/-- Sections over the inverse image of an open preserve countable products: a product of sheaves
of modules is computed open by open, and restriction of scalars preserves products.

Mathlib has the first half for `CategoryTheory.SheafOfModules`; it is not found by instance
search here because `AlgebraicGeometry.Scheme.Modules` is a `def`, so it is supplied as a
term. -/
instance preimageSectionsOver_preservesLimitsOfShape_discrete_nat :
    PreservesLimitsOfShape (Discrete ℕ) (preimageSectionsOver f V) :=
  @comp_preservesLimitsOfShape _ _ _ _ _ _ _ _ _ _
    (SheafOfModules.evaluationPreservesLimitsOfShape _ _ _)
    (preservesLimitsOfShape_restrictScalars _)

/-- **Unbounded derived sections over the inverse image of an open of the target**, read as a
functor out of the derived category of `AlgebraicGeometry.Scheme.Modules`. -/
abbrev derivedPreimageSectionsOver :
    DerivedCategory X.Modules ⥤ DerivedCategory
      (ModuleCat.{u} ((structureSheafRing S.toLocallyRingedSpace.toRingedSpace).obj.obj (op V))) :=
  derivedPreimageSections f.toLRSHom.toShHom V

/-- The canonical comparison exhibiting `derivedPreimageSectionsOver` as the right derived functor
of `preimageSectionsOver`. -/
abbrev derivedPreimageSectionsOverUnit :
    (preimageSectionsOver f V).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ derivedPreimageSectionsOver f V :=
  derivedPreimageSectionsUnit f.toLRSHom.toShHom V

/-- `derivedPreimageSectionsOver` is a right derived functor of `preimageSectionsOver`. -/
instance derivedPreimageSectionsOver_isRightDerivedFunctor :
    (derivedPreimageSectionsOver f V).IsRightDerivedFunctor
      (derivedPreimageSectionsOverUnit f V)
      (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)) :=
  inferInstanceAs ((derivedPreimageSections f.toLRSHom.toShHom V).IsRightDerivedFunctor
    (derivedPreimageSectionsUnit f.toLRSHom.toShHom V)
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (structureSheafRing X.toLocallyRingedSpace.toRingedSpace))
      (ComplexShape.up ℤ)))

/-- **The cohomology groups over `f⁻¹V` compute the higher right derived functors of sections over
`f⁻¹V`.** If `H^q(f⁻¹V, ℱ)` vanishes (a condition only when `q ≥ 0`), then the degree-`q` right
derived functor of sections over `f⁻¹V`, taken in `Γ(V, 𝒪_S)`-modules, vanishes at `ℱ`.

Module-valued sections over `f⁻¹V` followed by the forgetful functor to abelian groups *is* the
functor whose right derived functors are the cohomology groups `H^k(f⁻¹V, -)`, so deriving and
then forgetting agrees with the cohomology group
(`Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso`, the canonical half of
[Stacks, Tag 01F1]); the forgetful functor is faithful and additive, so it reflects the
vanishing. Restriction of scalars along `f^♯` is exact and may therefore be pulled out of the
right derived functor. In negative degrees there is nothing to prove.

The vanishing hypothesis is read on the single module `M` and the single degree `q`, and no
quasi-coherence is asked of `M`;
`AlgebraicGeometry.isZero_rightDerivedPlus_preimageSections_of_isZero_hgroup` is the same
conclusion from a uniform vanishing hypothesis over all quasi-coherent modules and all degrees
above a bound. -/
theorem isZero_rightDerivedPlus_preimageSections_of_isZero_hgroup' (M : X.Modules) (q : ℤ)
    (h : ∀ k : ℕ, q = (k : ℤ) → IsZero (Hgroup X.ringCatSheaf (f ⁻¹ᵁ V) k M)) :
    IsZero (((preimageSectionsOver f V).rightDerivedPlus q).obj M) := by
  by_cases hq : 0 ≤ q
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, q = (k : ℤ) := ⟨q.toNat, by omega⟩
    rw [Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff _ rfl]
    have hsecAdd : (secF X.ringCatSheaf (f ⁻¹ᵁ V)).Additive := secFAdditive _ _
    have hiso := @Stacks.Cohomology.ModuleComparison.rightDerivedCompIso _ _ _ _ _ _ _ _ _ _
      (preimageSectionsOver f V)
      (forget₂
        (ModuleCat.{u} ((structureSheafRing S.toLocallyRingedSpace.toRingedSpace).obj.obj (op V)))
        AddCommGrpCat.{u})
      (secF X.ringCatSheaf (f ⁻¹ᵁ V)) _ _ hsecAdd _ (Iso.refl _) k
    have hz : IsZero (((preimageSectionsOver f V).rightDerived k ⋙
        forget₂
          (ModuleCat.{u} ((structureSheafRing S.toLocallyRingedSpace.toRingedSpace).obj.obj (op V)))
          AddCommGrpCat.{u}).obj M) := (h k rfl).of_iso (hiso.app M)
    exact isZero_of_isZero_map (forget₂ (ModuleCat.{u}
      ((structureSheafRing S.toLocallyRingedSpace.toRingedSpace).obj.obj (op V)))
        AddCommGrpCat.{u}) hz
  · exact Stacks.RightDerivedPlus.isZero_rightDerivedPlus_obj _ q (by omega) M

end Sections

/-! ### Stacks 08D5, part (2) -/

section Clause2

open Stacks.Cohomology.DerivedSectionsLeray (derivedPreimageSections)

attribute [local instance] HasDerivedCategory.standard

/-- **A uniform shift of the upper cohomological bound under `Rf_*`.** For a quasi-compact and
quasi-separated `f : X ⟶ S` with `S` quasi-compact there is an integer `N` such that every object
`E` of `D_QCoh(𝒪_X)` living in degrees `≤ b` has `H^m(Rf_*E) = 0` for `m ≥ b + N`.

Let `ℬ` be the basis of affine opens and `N` the degree of
`AlgebraicGeometry.exists_isZero_hgroup_preimage_isBasis`. For `V ∈ ℬ` the higher right derived
functors of `Γ(f⁻¹V, -)` vanish in degrees `≥ N` on quasi-coherent modules, so [Stacks, Tag 08D4]
part (3) bounds `RΓ(f⁻¹V, E)` above by `b + N - 1`; by [Stacks, Tag 0D5W] that is `RΓ(V, Rf_*E)`,
and a cohomology sheaf of `Rf_*E` vanishes as soon as the hypercohomology over the inverse images
of a basis does ([Stacks, Tag 0D66], resting on [Stacks, Tag 0D5X]).

This is the form [Stacks, Tag 08D5] part (1) consumes: there the bound is applied to the
truncations `τ_{≤ -n-1}E`, whose upper bound tends to `-∞`. Part (2) of the source is the case
`b = 0`. -/
theorem exists_isZero_homology_derivedPushforward (f : X ⟶ S) [QuasiCompact f]
    [QuasiSeparated f] [CompactSpace S] :
    ∃ N : ℤ, ∀ E : DerivedCategory X.Modules,
      (∀ j : ℤ, ((DerivedCategory.homologyFunctor X.Modules j).obj E).IsQuasicoherent) →
      ∀ b : ℤ, E.IsLE b → ∀ m : ℤ, b + N ≤ m →
      IsZero ((DerivedCategory.homologyFunctor S.Modules m).obj
        ((RingedSpace.derivedPushforward f.toLRSHom.toShHom).obj E)) := by
  obtain ⟨ℬ, N, hℬ, -, hvan⟩ := exists_isZero_hgroup_preimage_isBasis f
  refine ⟨(N : ℤ), fun E hcoh b hE m hm ↦ ?_⟩
  refine Stacks.Cohomology.UnboundedHigherDirectImage.isZero_homologyDerivedPushforward_of_isBasis
    f.toLRSHom.toShHom hℬ E m fun V hV ↦ ?_
  have hbound : ((derivedPreimageSectionsOver f V).obj E).IsLE (b + (N : ℤ) - 1) :=
    isLE_rightDerivedFunctor_obj_of_isZero X (preimageSectionsOver f V)
      (derivedPreimageSectionsOver f V) (derivedPreimageSectionsOverUnit f V) N
      (fun M hM p hp ↦ isZero_rightDerivedPlus_preimageSections_of_isZero_hgroup' f V M p
        fun k hk ↦ hvan V hV M hM k (by omega))
      E hcoh b hE
  exact ((derivedPreimageSectionsOver f V).obj E).isZero_of_isLE (b + (N : ℤ) - 1) m (by omega)

/-- **[Stacks, Tag 08D5], part (2).** Let `f : X ⟶ S` be a quasi-compact and quasi-separated
morphism of schemes with `S` quasi-compact. There is an integer `N`, depending on `X`, `S` and `f`
alone, such that every object `E` of `D_QCoh(𝒪_X)` with `H^m(E) = 0` for `m > 0` has
`H^m(Rf_*E) = 0` for `m ≥ N`.

This is `AlgebraicGeometry.exists_isZero_homology_derivedPushforward` at `b = 0`. -/
@[stacks 08D5 "part (2)"]
theorem exists_isZero_homology_derivedPushforward_of_isLE (f : X ⟶ S) [QuasiCompact f]
    [QuasiSeparated f] [CompactSpace S] :
    ∃ N : ℤ, ∀ E : QuasicoherentDerivedCategory X, E.obj.IsLE 0 → ∀ m : ℤ, N ≤ m →
      IsZero ((DerivedCategory.homologyFunctor S.Modules m).obj
        ((RingedSpace.derivedPushforward f.toLRSHom.toShHom).obj E.obj)) := by
  obtain ⟨N, hN⟩ := exists_isZero_homology_derivedPushforward f
  exact ⟨N, fun E hE m hm ↦ hN E.obj (fun j ↦ E.property j) 0 hE m (by omega)⟩

end Clause2

end AlgebraicGeometry

end
