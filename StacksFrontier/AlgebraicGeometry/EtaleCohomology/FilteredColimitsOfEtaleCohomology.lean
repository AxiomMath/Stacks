module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ConstantSheafInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleAbelianDerivedFunctors
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FilteredColimits.SectionsOnALocallySmallSite
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.DerivedGlobalSectionsCohomology
public import StacksCore.Tactic.StacksAttribute

/-!
# Étale cohomology commutes with filtered colimits

Let `X` be a quasi-compact and quasi-separated scheme. Then for every `p` the canonical map

> `colim_i H^p_étale(X, F_i) ⟶ H^p_étale(X, colim_i F_i)`

is an isomorphism, for every filtered system `F` of abelian sheaves on the small étale site of
`X`. This is Stacks 03Q5.

The site-level statement is Stacks 0739: on a site carrying a collection `B` of objects which
admits cofinal *finite* covering families whose iterated fibre products stay in `B`, filtered
colimits of abelian sheaves commute with cohomology over every object of `B`. It is available at
the universes of the small étale site as
`Stacks.Cohomology.isIso_colimit_post_rightDerived_sheafSections_largeCoefficients`. This file
supplies its three hypotheses for the small étale site of a scheme, with `B` the collection
`Stacks.EtaleCohomology.qcSeparatedOver X` of objects quasi-compact and separated over `X`.

## Main results

* `Stacks.EtaleCohomology.exists_qcSepCovering_le` — the cofinal finite affine refinement: over a
  quasi-compact and quasi-separated base, a covering sieve of an object quasi-compact and
  separated over `X` contains a finite covering family by objects with affine underlying scheme.
* `Stacks.EtaleCohomology.exists_pullbackCone_mem_qcSeparatedOver` — being quasi-compact and
  separated over `X` is inherited by a fibre product of two such objects over a third.
* `Stacks.EtaleCohomology.isIso_colimit_post_rightDerived_sheafSections_smallEtale` — filtered
  colimits commute with cohomology over any object quasi-compact and separated over `X`.
* `Stacks.EtaleCohomology.isIso_colimit_post_rightDerived_Γ_smallEtale` — Stacks 03Q5: filtered
  colimits commute with the étale cohomology of `X` itself.

## Implementation notes

Coefficients are `AddCommGrpCat.{max (u + 1) v}` for a scheme universe `u` and arbitrary `v`,
matching the rest of the étale abelian development; the small étale site of `X : Scheme.{u}` has
its objects in `Type (u + 1)` and its morphisms in `Type u`, so this is the first universe in
which sheafification is available.

The collection `B` is taken to be the objects `V` of `X.Etale` with `V.hom` quasi-compact and
separated, rather than with `V.left` quasi-compact and quasi-separated as in the source: over a
quasi-compact and quasi-separated base the two agree, and the relative form is what the stability
proofs use. `X` itself qualifies, which is what makes the étale cohomology of `X` a case of the
statement over an object of `B`.

Étale cohomology of `X` is the right derived functor of Mathlib's global sections functor
`CategoryTheory.Sheaf.Γ`, identified with sections over the final object `X ⟶ X` of the small
étale site by `CategoryTheory.Sheaf.ΓNatIsoSheafSections`.

Several `MorphismProperty` classes of `@Etale` — stability under composition, containing the
identities, invariance under isomorphism — are supplied here as local instances: Mathlib declares
them only through `MorphismProperty.IsMultiplicative @Etale`, whose parent projections are not
instances, so the pretopology lemmas for the small étale site do not elaborate without them.

## References

* [Stacks Project, Tag 03Q5](https://stacks.math.columbia.edu/tag/03Q5)
* [Stacks Project, Tag 0739](https://stacks.math.columbia.edu/tag/0739)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe v u

namespace Stacks.EtaleCohomology

noncomputable section

variable {X : Scheme.{u}}

/-! ### Étale morphisms as site-theoretic input -/

/-- Being étale is invariant under isomorphisms of the source and of the target. -/
theorem etale_respectsIso :
    MorphismProperty.RespectsIso (@Etale : MorphismProperty Scheme.{u}) :=
  MorphismProperty.IsStableUnderBaseChange.respectsIso

attribute [local instance] AlgebraicGeometry.Etale.isStableUnderComposition
  Stacks.EtaleCohomology.etaleContainsIdentities etale_respectsIso

attribute [local instance] Stacks.Cohomology.ColimitsOfCohomology.additive_sheafΓ

/-! ### Images of open subschemes -/

/-- The range of `W.ι ≫ f` is the image under `f` of the open set `W`. -/
theorem range_opensι_comp {Y Z : Scheme.{u}} (W : Y.Opens) (f : Y ⟶ Z) :
    Set.range (W.ι ≫ f) = f '' (W : Set Y) := by
  simp [Set.range_comp]

/-- The image of an open subscheme under an étale morphism is open. -/
theorem isOpen_range_opensι_comp {Y Z : Scheme.{u}} (W : Y.Opens) (f : Y ⟶ Z) [Etale f] :
    IsOpen (Set.range (W.ι ≫ f)) := by
  rw [range_opensι_comp]
  exact f.isOpenMap _ W.isOpen

/-- A point of an open subscheme is carried into the range of the composite of the inclusion
with any morphism. -/
theorem mem_range_opensι_comp {Y Z : Scheme.{u}} (W : Y.Opens) (f : Y ⟶ Z) {p : Y} {q : Z}
    (hp : p ∈ W) (hq : f p = q) : q ∈ Set.range (W.ι ≫ f) := by
  rw [range_opensι_comp]
  exact ⟨p, hp, hq⟩

/-! ### Objects quasi-compact and separated over the base -/

/-- The objects of the small étale site of `X` whose structure morphism is quasi-compact and
separated. Over a quasi-compact and quasi-separated base these are the objects over which the
étale cohomology can be computed by finite coverings, by
`Stacks.EtaleCohomology.exists_qcSepCovering_le`. -/
def qcSeparatedOver (X : Scheme.{u}) : Set X.Etale :=
  {V | QuasiCompact V.hom ∧ IsSeparated V.hom}

variable (X) in
/-- `X` itself is quasi-compact and separated over `X`. -/
theorem etaleMkId_mem_qcSeparatedOver : Scheme.Etale.mk (𝟙 X) ∈ qcSeparatedOver X :=
  ⟨show QuasiCompact (𝟙 X) from inferInstance, show IsSeparated (𝟙 X) from inferInstance⟩

/-- An object of the small étale site of a quasi-separated scheme whose underlying scheme is
affine is quasi-compact and separated over the base. -/
theorem mem_qcSeparatedOver_of_isAffine [QuasiSeparatedSpace X] (V : X.Etale)
    [IsAffine V.left] : V ∈ qcSeparatedOver X :=
  ⟨show QuasiCompact (V.left ↘ X) from inferInstance,
    show IsSeparated (V.left ↘ X) from inferInstance⟩

/-- The underlying scheme of an object quasi-compact over a quasi-compact base is
quasi-compact. -/
theorem compactSpace_left_of_mem_qcSeparatedOver [CompactSpace X] {V : X.Etale}
    (hV : V ∈ qcSeparatedOver X) : CompactSpace V.left := by
  have hX : CompactSpace ↥((Functor.fromPUnit X).obj V.right) :=
    inferInstanceAs (CompactSpace ↥X)
  have := hV.1
  exact QuasiCompact.compactSpace_of_compactSpace V.hom

/-- A morphism between objects quasi-compact and separated over `X` is itself quasi-compact and
separated: it is cancelled out of the composite with the structure morphism of its target, which
is separated and hence quasi-separated. -/
theorem quasiCompact_isSeparated_left_of_mem_qcSeparatedOver {V W : X.Etale} (h : V ⟶ W)
    (hV : V ∈ qcSeparatedOver X) (hW : W ∈ qcSeparatedOver X) :
    QuasiCompact h.left ∧ IsSeparated h.left := by
  have hw : h.left ≫ W.hom = V.hom := MorphismProperty.Over.w h
  have h₁ : QuasiCompact (h.left ≫ W.hom) := hw ▸ hV.1
  have h₂ : IsSeparated (h.left ≫ W.hom) := hw ▸ hV.2
  have h₃ := hW.2
  exact ⟨QuasiCompact.of_comp h.left W.hom, IsSeparated.of_comp h.left W.hom⟩

/-- The objects quasi-compact and separated over `X` contain the vertex of a fibre product of any
two of their members over any third: the first projection is a base change of a morphism which is
quasi-compact and separated, and composing it with the structure morphism of the first factor
keeps both properties. -/
theorem exists_pullbackCone_mem_qcSeparatedOver {V₁ V₂ W : X.Etale} (f : V₁ ⟶ W) (g : V₂ ⟶ W)
    (h₁ : V₁ ∈ qcSeparatedOver X) (h₂ : V₂ ∈ qcSeparatedOver X) (hW : W ∈ qcSeparatedOver X) :
    ∃ t : PullbackCone f g, Nonempty (IsLimit t) ∧ t.pt ∈ qcSeparatedOver X := by
  obtain ⟨hg₁, hg₂⟩ := quasiCompact_isSeparated_left_of_mem_qcSeparatedOver g h₂ hW
  have hsq : IsPullback (pullback.snd f g).left (pullback.fst f g).left g.left f.left :=
    ((IsPullback.of_hasPullback f g).map
      (Scheme.Etale.forget X ⋙ CategoryTheory.Over.forget X)).flip
  have hq : QuasiCompact (pullback.fst f g).left :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq hg₁
  have hs : IsSeparated (pullback.fst f g).left :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq hg₂
  have hw : (pullback.fst f g).left ≫ V₁.hom = (pullback f g).hom :=
    MorphismProperty.Over.w _
  have hA := h₁.1
  have hB := h₁.2
  refine ⟨PullbackCone.mk (pullback.fst f g) (pullback.snd f g) pullback.condition,
    ⟨pullbackIsPullback f g⟩, ?_, ?_⟩
  · exact hw ▸ (inferInstance : QuasiCompact ((pullback.fst f g).left ≫ V₁.hom))
  · exact hw ▸ (inferInstance : IsSeparated ((pullback.fst f g).left ≫ V₁.hom))

/-! ### Cofinal finite coverings -/

/-- A sieve covering for the small étale pretopology contains, through each point of the object it
covers, an étale morphism hitting that point. -/
theorem exists_mem_of_mem_toGrothendieck_smallEtalePretopology (U : X.Etale) (R : Sieve U)
    (hR : R ∈ X.smallEtalePretopology.toGrothendieck U) (x : U.left) :
    ∃ (Y : X.Etale) (g : Y ⟶ U) (y : Y.left), R g ∧ Etale g.left ∧ g.left y = x :=
  (Scheme.mem_toGrothendieck_smallPretopology U R).1 hR x

/-- A covering sieve of the small étale site contains, through each point of the object it covers,
an étale morphism hitting that point. -/
theorem exists_mem_of_mem_smallEtaleTopology (U : X.Etale) (R : Sieve U)
    (hR : R ∈ X.smallEtaleTopology U) (x : U.left) :
    ∃ (Y : X.Etale) (g : Y ⟶ U) (y : Y.left), R g ∧ Etale g.left ∧ g.left y = x :=
  exists_mem_of_mem_toGrothendieck_smallEtalePretopology U R
    ((Scheme.smallGrothendieckTopology_eq_toGrothendieck_smallPretopology X (P := @Etale)
      le_rfl).le U hR) x

/-- The finite covering families of an object of the small étale site by objects quasi-compact and
separated over `X`. -/
def qcSepCovering (X : Scheme.{u}) (U : X.Etale) : Set (PreZeroHypercover.{u} U) :=
  {E | Finite E.I₀ ∧ U ∈ qcSeparatedOver X ∧ (∀ i, E.X i ∈ qcSeparatedOver X) ∧
    E.sieve₀ ∈ X.smallEtaleTopology U}

/-- **Cofinal finite affine refinement.** Every covering sieve of an object `U` of the small
étale site whose underlying scheme is quasi-compact contains a finite covering family by objects
with affine underlying scheme.

Each point of `U` is hit by some member of the sieve; shrinking that member to an affine open
neighbourhood of a preimage of the point keeps it in the sieve and still covers an open subset of
`U` containing the point, étale morphisms being open. Quasi-compactness of `U` then selects
finitely many of these. -/
theorem exists_finite_isAffine_covering_le (U : X.Etale) [CompactSpace U.left] (R : Sieve U)
    (hR : R ∈ X.smallEtaleTopology U) :
    ∃ E : PreZeroHypercover.{u} U, Finite E.I₀ ∧ (∀ i, IsAffine (E.X i).left) ∧
      E.sieve₀ ∈ X.smallEtaleTopology U ∧ E.sieve₀ ≤ R := by
  classical
  choose Y g y hRg hEg hgy using exists_mem_of_mem_smallEtaleTopology U R hR
  have haff : ∀ x : U.left, ∃ W : (Y x).left.Opens, IsAffineOpen W ∧ y x ∈ W := by
    intro x
    obtain ⟨W, hW, hy, -⟩ :=
      exists_isAffineOpen_mem_and_subset (TopologicalSpace.Opens.mem_top (y x))
    exact ⟨W, hW, hy⟩
  choose W hWaff hWmem using haff
  let V : U.left → X.Etale := fun x ↦ Scheme.Etale.mk ((W x).ι ≫ ((Y x).left ↘ X))
  let a : ∀ x, V x ⟶ Y x := fun x ↦ MorphismProperty.Over.homMk (W x).ι rfl trivial
  let h : ∀ x, V x ⟶ U := fun x ↦ a x ≫ g x
  have hopen : ∀ x, IsOpen (Set.range (h x).left) := fun x ↦
    isOpen_range_opensι_comp (W x) (g x).left
  have hmem : ∀ x, x ∈ Set.range (h x).left := fun x ↦
    mem_range_opensι_comp (W x) (g x).left (hWmem x) (hgy x)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x : U.left ↦ Set.range (h x).left) hopen
    (fun x _ ↦ Set.mem_iUnion.2 ⟨x, hmem x⟩)
  refine ⟨{ I₀ := {x : U.left // x ∈ t}, X := fun i ↦ V i.1, f := fun i ↦ h i.1 },
    inferInstance, fun i ↦ hWaff i.1, ?_, ?_⟩
  · refine (Scheme.ofArrows_mem_smallEtaleTopology_iff _).2 ?_
    refine Set.eq_univ_of_subset ?_ (Set.eq_univ_of_univ_subset ht)
    simp only [Set.iUnion_subset_iff]
    intro i hi
    exact Set.subset_iUnion_of_subset ⟨i, hi⟩ le_rfl
  · rw [Sieve.generate_le_iff]
    rintro Z u ⟨i⟩
    exact R.downward_closed (hRg i.1) (a i.1)

/-- **Cofinal finite affine refinement.** Over a quasi-compact and quasi-separated scheme `X`,
every covering sieve of an object `U` of the small étale site which is quasi-compact and separated
over `X` contains a finite covering family by objects with affine underlying scheme, in particular
by objects quasi-compact and separated over `X`.

This is `Stacks.EtaleCohomology.exists_finite_isAffine_covering_le`, the underlying scheme of `U`
being quasi-compact. -/
theorem exists_qcSepCovering_le [CompactSpace X] [QuasiSeparatedSpace X] (U : X.Etale)
    (hU : U ∈ qcSeparatedOver X) (R : Sieve U) (hR : R ∈ X.smallEtaleTopology U) :
    ∃ E ∈ qcSepCovering X U, E.sieve₀ ≤ R := by
  have hcs : CompactSpace U.left := compactSpace_left_of_mem_qcSeparatedOver hU
  obtain ⟨E, hfin, haff, hE, hle⟩ := exists_finite_isAffine_covering_le U R hR
  exact ⟨E, ⟨hfin, hU, fun i ↦ have := haff i; mem_qcSeparatedOver_of_isAffine _, hE⟩, hle⟩

/-- A finite covering family by objects quasi-compact and separated over `X` has all its iterated
fibre products quasi-compact and separated over `X`, by induction on the family from the binary
case. -/
theorem hasIntersectionsIn_qcSeparatedOver (U : X.Etale) (E : PreZeroHypercover.{u} U)
    (hE : E ∈ qcSepCovering X U) :
    Stacks.Cohomology.HasIntersectionsIn (qcSeparatedOver X) E :=
  ⟨hE.1, hE.2.1, hE.2.2.1, fun n A ↦ Stacks.Cohomology.exists_widePullback_in
    (qcSeparatedOver X) (fun f g hu hv hw ↦ exists_pullbackCone_mem_qcSeparatedOver f g hu hv hw)
    hE.2.1 (n + 1) (fun i ↦ E.X (A i)) (fun i ↦ E.f (A i)) (fun i ↦ hE.2.2.1 (A i))⟩

/-! ### Filtered colimits and étale cohomology -/

/-- **Étale cohomology over a quasi-compact separated object commutes with filtered colimits.**
Over a quasi-compact and quasi-separated scheme `X`, for every object `U` of the small étale site
which is quasi-compact and separated over `X`, every degree `p` and every filtered system `F` of
abelian sheaves, the canonical map from the filtered colimit of the cohomology groups over `U` to
the cohomology of the filtered colimit is an isomorphism.

This is Stacks 0739 on the small étale site: the finite coverings by objects quasi-compact and
separated over `X` are cofinal among the coverings of such a `U`, and their iterated fibre
products are again such objects. -/
theorem isIso_colimit_post_rightDerived_sheafSections_smallEtale
    [CompactSpace X] [QuasiSeparatedSpace X] (p : ℕ) (U : X.Etale)
    (hU : U ∈ qcSeparatedOver X) {I : Type (max (u + 1) v)} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :
    IsIso (colimit.post F (((sheafSections X.smallEtaleTopology
      AddCommGrpCat.{max (u + 1) v}).obj (op U)).rightDerived p)) :=
  Stacks.Cohomology.isIso_colimit_post_rightDerived_sheafSections_largeCoefficients.{v, u, u, u + 1}
    X.smallEtaleTopology (qcSeparatedOver X) (qcSepCovering X)
    (fun _ _ hE ↦ hE.2.2.2) (fun U E hE ↦ hasIntersectionsIn_qcSeparatedOver U E hE)
    (fun U hU R hR ↦ exists_qcSepCovering_le U hU R hR) p U hU F

/-- **Stacks 03Q5.** Let `X` be a quasi-compact and quasi-separated scheme. For every degree `p`
and every filtered system `F` of abelian sheaves on the small étale site of `X`, the canonical map

> `colim_i H^p_étale(X, F_i) ⟶ H^p_étale(X, colim_i F_i)`

is an isomorphism: taking cohomology of the étale site of `X` commutes with filtered colimits.

Étale cohomology is the right derived functor of global sections, which is sections over the final
object `X ⟶ X` of the small étale site; that object is quasi-compact and separated over `X`, so
this is the case `U = X` of
`Stacks.EtaleCohomology.isIso_colimit_post_rightDerived_sheafSections_smallEtale`. -/
@[stacks 03Q5]
theorem isIso_colimit_post_rightDerived_Γ_smallEtale (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] (p : ℕ)
    {I : Type (max (u + 1) v)} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :
    IsIso (colimit.post F
      ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).rightDerived p)) := by
  have := isIso_colimit_post_rightDerived_sheafSections_smallEtale.{v} p
    (Scheme.Etale.mk (𝟙 X)) (etaleMkId_mem_qcSeparatedOver X) F
  exact Stacks.Cohomology.isIso_colimit_post_of_natIso F _ _
    (Stacks.Cohomology.CompositeRightDerived.rightDerivedNatIso
      (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}
        (show IsTerminal (Scheme.Etale.mk (𝟙 X)) from
          MorphismProperty.Over.mkIdTerminal _ _)) p).symm

end

end Stacks.EtaleCohomology

end
