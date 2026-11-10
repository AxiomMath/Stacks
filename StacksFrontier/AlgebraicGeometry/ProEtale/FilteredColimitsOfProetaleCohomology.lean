module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.AbelianSheafification
public import StacksFrontier.AlgebraicGeometry.ProEtale.SiteFunctoriality.AffineDenseSubsite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FilteredColimits.SectionsOnALocallySmallSite
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.DerivedGlobalSectionsCohomology
public import StacksCore.Tactic.StacksAttribute

/-!
# Pro-étale cohomology commutes with filtered colimits

Let `X` be a quasi-compact and quasi-separated scheme. Then for every `p` the canonical map

> `colim_i H^p(U_pro-étale, F_i) ⟶ H^p(U_pro-étale, colim_i F_i)`

is an isomorphism, for every filtered system `F` of abelian sheaves on the small pro-étale site
of `X` and every object `U` of that site which is quasi-compact and quasi-separated.

The site-level statement is Stacks 0739: on a site carrying a collection `B` of objects which
admits cofinal *finite* covering families whose iterated fibre products stay in `B`, filtered
colimits of abelian sheaves commute with cohomology over every object of `B`. It is available
at the universes of the small pro-étale site as
`Stacks.Cohomology.isIso_colimit_post_rightDerived_sheafSections_largeCoefficients`. This file
supplies its three hypotheses for the small pro-étale site of a scheme, with `B` the collection
`AlgebraicGeometry.ProEtale.qcqsObjects X` of objects whose underlying scheme is quasi-compact
and quasi-separated.

## Main definitions

* `AlgebraicGeometry.ProEtale.qcqsObjects`: the objects of the small pro-étale site whose
  underlying scheme is quasi-compact and quasi-separated.
* `AlgebraicGeometry.ProEtale.qcqsCovering`: the finite covering families of such an object all
  of whose members have affine underlying scheme.

## Main results

* `AlgebraicGeometry.ProEtale.exists_qcqsCovering_le`: the cofinal finite affine refinement —
  over a quasi-compact and quasi-separated base, every covering sieve of a quasi-compact
  quasi-separated object of the small pro-étale site contains a finite covering family by
  objects with affine underlying scheme.
* `AlgebraicGeometry.ProEtale.exists_pullbackCone_mem_qcqsObjects`: being quasi-compact and
  quasi-separated is inherited by a fibre product of two such objects over a third.
* `AlgebraicGeometry.ProEtale.isIso_colimit_post_rightDerived_sheafSections_proetale`: filtered
  colimits commute with cohomology over any quasi-compact quasi-separated object.
* `AlgebraicGeometry.ProEtale.isIso_colimit_post_rightDerived_Γ_proetale`: the same for the
  pro-étale cohomology of `X` itself.

## Implementation notes

The refinement is produced from the quasi-compactness of the covering families of the
pro-étale precoverage rather than from openness of the members, which is how the étale
argument of `Stacks.EtaleCohomology.exists_qcSepCovering_le` proceeds: a weakly étale morphism
need not be open on underlying spaces, so a member of a covering sieve cannot be shrunk to an
affine open neighbourhood and still cover an open set. Instead
`CategoryTheory.Limits.QuasiCompactCover.exists_hom` refines the covering family by one indexed
by a finite set of affine schemes, and `IsCompactOpenCovered.of_finite_of_isSpectralMap` checks
that the refinement is again a quasi-compact cover.

Coefficients are `AddCommGrpCat.{max (u + 1) v}` for a scheme universe `u` and arbitrary `v`:
the small pro-étale site of `X : Scheme.{u}` has its objects in `Type (u + 1)` and its
morphisms in `Type u`, so this is the first universe in which sheafification is available.

Pro-étale cohomology of `X` is the right derived functor of Mathlib's global sections functor
`CategoryTheory.Sheaf.Γ`, identified with sections over the final object `X ⟶ X` of the small
pro-étale site by `CategoryTheory.Sheaf.ΓNatIsoSheafSections`.

## References

* [Stacks Project, Tag 0739](https://stacks.math.columbia.edu/tag/0739)
* [Stacks Project, Tag 098K](https://stacks.math.columbia.edu/tag/098K)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry.ProEtale

variable {X : Scheme.{u}}

/-! ### Quasi-compact quasi-separated objects -/

/-- The objects of the small pro-étale site of `X` whose underlying scheme is quasi-compact and
quasi-separated. These are the objects over which pro-étale cohomology can be computed by finite
coverings, by `AlgebraicGeometry.ProEtale.exists_qcqsCovering_le`. -/
def qcqsObjects (X : Scheme.{u}) : Set X.ProEt :=
  {U | CompactSpace U.left ∧ QuasiSeparatedSpace U.left}

variable (X) in
/-- `X` itself, as the identity object, is quasi-compact and quasi-separated as soon as it is. -/
theorem proEtMkId_mem_qcqsObjects [CompactSpace X] [QuasiSeparatedSpace X] :
    Scheme.ProEt.mk (𝟙 X) ∈ qcqsObjects X :=
  ⟨inferInstanceAs (CompactSpace X), inferInstanceAs (QuasiSeparatedSpace X)⟩

/-- A fibre product of two quasi-compact quasi-separated objects of the small pro-étale site
over a quasi-separated one is again quasi-compact and quasi-separated: the forgetful functor to
schemes preserves the fibre product, and a fibre product of quasi-compact schemes over a
quasi-separated one is quasi-compact. -/
theorem compactSpace_quasiSeparatedSpace_pullback {U V W : X.ProEt} (f : V ⟶ U) (g : W ⟶ U)
    [QuasiSeparatedSpace U.left] [CompactSpace V.left] [QuasiSeparatedSpace V.left]
    [CompactSpace W.left] [QuasiSeparatedSpace W.left] :
    CompactSpace (pullback f g).left ∧ QuasiSeparatedSpace (pullback f g).left := by
  let q := Scheme.ProEt.forget X ⋙ Over.forget X
  let e := PreservesPullback.iso q f g
  have : CompactSpace ↥(pullback (q.map f) (q.map g) : Scheme) := by
    change CompactSpace ↥(pullback f.left g.left : Scheme)
    infer_instance
  have : QuasiSeparatedSpace ↥(pullback (q.map f) (q.map g) : Scheme) := by
    change QuasiSeparatedSpace ↥(pullback f.left g.left : Scheme)
    exact quasiSeparatedSpace_of_quasiSeparated (pullback.fst f.left g.left)
  exact ⟨e.inv.homeomorph.compactSpace,
    (quasiSeparatedSpace_congr e.hom.homeomorph).mpr inferInstance⟩

/-- The quasi-compact quasi-separated objects of the small pro-étale site contain the vertex of
a fibre product of any two of their members over any third. -/
theorem exists_pullbackCone_mem_qcqsObjects {V W U : X.ProEt} (f : V ⟶ U) (g : W ⟶ U)
    (hV : V ∈ qcqsObjects X) (hW : W ∈ qcqsObjects X) (hU : U ∈ qcqsObjects X) :
    ∃ t : PullbackCone f g, Nonempty (IsLimit t) ∧ t.pt ∈ qcqsObjects X := by
  have := hU.2
  have := hV.1
  have := hV.2
  have := hW.1
  have := hW.2
  refine ⟨PullbackCone.mk (pullback.fst f g) (pullback.snd f g) pullback.condition,
    ⟨pullbackIsPullback f g⟩, ?_⟩
  exact compactSpace_quasiSeparatedSpace_pullback f g

/-! ### Cofinal finite affine coverings -/

/-- **Cofinal finite affine refinement.** Every covering sieve of a quasi-compact
quasi-separated object `U` of the small pro-étale site contains a finite covering family all of
whose members have affine underlying scheme.

A covering sieve contains a chosen pro-étale covering family of `U`, which is in particular a
quasi-compact cover of the underlying scheme; `QuasiCompactCover.exists_hom` refines it by a
finite family of affine schemes mapping into its members, and that refinement is again a
quasi-compact cover because finitely many affine schemes mapping by spectral maps onto a cover
do cover. Each member of the refinement is weakly étale over `X`, being the composite of a
morphism into a member of the family with that member's structure morphism, so it is again an
object of the site. -/
theorem exists_finite_affine_covering_le (U : X.ProEt) [CompactSpace U.left]
    [QuasiSeparatedSpace U.left] (S : Sieve U) (hS : S ∈ Scheme.ProEt.topology X U) :
    ∃ E : PreZeroHypercover.{u + 1} U, Finite E.I₀ ∧
      E.presieve₀ ∈ Scheme.ProEt.precoverage X U ∧ E.sieve₀ ≤ S ∧
      ∀ i, IsAffine (E.X i).left := by
  classical
  let : (Scheme.ProEt.precoverage X).IsStableUnderComposition := by
    dsimp [Scheme.ProEt.precoverage]; infer_instance
  let : (Scheme.ProEt.precoverage X).IsStableUnderBaseChange := by
    dsimp [Scheme.ProEt.precoverage]; infer_instance
  let : (Scheme.ProEt.precoverage X).HasIsos := by
    dsimp [Scheme.ProEt.precoverage]; infer_instance
  obtain ⟨R, hR, hRS⟩ := Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition.mp hS
  obtain ⟨E, hER⟩ := Precoverage.mem_iff_exists_zeroHypercover.mp hR
  let q := Scheme.ProEt.forget X ⋙ Over.forget X
  have hE : (E.toPreZeroHypercover.map q).presieve₀ ∈ Scheme.proetalePrecoverage U.left := by
    rw [PreZeroHypercover.presieve₀_map]
    exact E.mem₀
  let V₀ : U.left.Cover (Scheme.precoverage @WeaklyEtale) :=
    { E.toPreZeroHypercover.map q with mem₀ := hE.2 }
  let : QuasiCompactCover V₀.toPreZeroHypercover :=
    Scheme.presieve₀_mem_qcPrecoverage_iff.mp hE.1
  let : MorphismProperty.RespectsLeft @WeaklyEtale @IsOpenImmersion := ⟨by
    intro A B C i hi f hf
    let : Etale i := inferInstance
    let : WeaklyEtale i := inferInstance
    exact inferInstance⟩
  obtain ⟨V, f, hfin, hopen⟩ := QuasiCompactCover.exists_hom V₀
  let := hfin
  let Vobj (i : V.I₀) : X.ProEt := by
    let : WeaklyEtale (V.cover.f i) := V.cover.map_prop i
    exact Scheme.ProEt.mk (V.cover.f i ≫ U.hom)
  let F : PreZeroHypercover.{u + 1} U :=
    { I₀ := V.I₀, X := Vobj, f i := MorphismProperty.Over.homMk (V.cover.f i) rfl }
  have hMap : F.map q = V.cover.toPreZeroHypercover := by
    apply PreZeroHypercover.ext rfl
    all_goals simp [F, Vobj, q, Scheme.ProEt.forget, MorphismProperty.Over.forget,
      MorphismProperty.Comma.forget, Over.forget, Scheme.ProEt.mk]
  have haff (i : V.I₀) : IsAffine (V.cover.X i) := inferInstanceAs (IsAffine (Spec (V.X i)))
  have hVqc : QuasiCompactCover V.cover.toPreZeroHypercover := by
    have : Finite V.cover.I₀ := hfin
    exact ⟨fun {W} hW => IsCompactOpenCovered.of_finite_of_isSpectralMap
      (fun i => by
        let := haff i
        let : QuasiCompact (V.cover.f i) := quasiCompact_of_compactSpace _
        exact (V.cover.f i).isSpectralMap)
      (fun x _ => ⟨V.idx x, V.covers x⟩) W.2 hW.isCompact⟩
  refine ⟨F, hfin, ?_, ?_, haff⟩
  · change Presieve.map q F.presieve₀ ∈ Scheme.proetalePrecoverage U.left
    rw [← PreZeroHypercover.presieve₀_map, hMap]
    exact ⟨Scheme.presieve₀_mem_qcPrecoverage_iff.mpr hVqc, V.cover.mem₀⟩
  · apply (Sieve.generate_le_iff _ _).mpr
    rintro Y g ⟨i⟩
    let a : F.X i ⟶ E.X (f.s₀ i) :=
      MorphismProperty.Over.homMk (f.h₀ i) (by
        change f.h₀ i ≫ (E.X (f.s₀ i)).hom = V.cover.f i ≫ U.hom
        rw [← f.w₀ i, Category.assoc]
        exact congrArg (fun k => f.h₀ i ≫ k) (E.f (f.s₀ i)).w.symm)
    have ha : a ≫ E.f (f.s₀ i) = F.f i := MorphismProperty.Over.Hom.ext (f.w₀ i)
    rw [← ha]
    apply S.downward_closed
    apply hRS
    rw [hER]
    exact Presieve.ofArrows.mk _

/-- The finite covering families of an object of the small pro-étale site by objects with affine
underlying scheme, all of whose iterated fibre products are quasi-compact and
quasi-separated. -/
def qcqsCovering (X : Scheme.{u}) (U : X.ProEt) : Set (PreZeroHypercover.{u + 1} U) :=
  {E | Stacks.Cohomology.HasIntersectionsIn (qcqsObjects X) E ∧
    E.presieve₀ ∈ Scheme.ProEt.precoverage X U ∧ ∀ i, IsAffine (E.X i).left}

/-- A covering family of `qcqsCovering` is a covering family of the small pro-étale
topology. -/
theorem sieve₀_mem_topology_of_mem_qcqsCovering (U : X.ProEt)
    (E : PreZeroHypercover.{u + 1} U) (hE : E ∈ qcqsCovering X U) :
    E.sieve₀ ∈ Scheme.ProEt.topology X U :=
  Precoverage.generate_mem_toGrothendieck hE.2.1

/-- **The finite affine coverings are cofinal.** Every covering sieve of a quasi-compact
quasi-separated object of the small pro-étale site contains a member of `qcqsCovering`. -/
theorem exists_qcqsCovering_le (U : X.ProEt) (hU : U ∈ qcqsObjects X)
    (S : Sieve U) (hS : S ∈ Scheme.ProEt.topology X U) :
    ∃ E ∈ qcqsCovering X U, E.sieve₀ ≤ S := by
  have := hU.1
  have := hU.2
  obtain ⟨E, hfin, hcover, hle, haff⟩ := exists_finite_affine_covering_le U S hS
  have hmember (i : E.I₀) : E.X i ∈ qcqsObjects X := by
    have : IsAffine (E.X i).left := haff i
    exact ⟨inferInstance, inferInstance⟩
  refine ⟨E, ⟨⟨hfin, hU, hmember, fun n A ↦ ?_⟩, hcover, haff⟩, hle⟩
  exact Stacks.Cohomology.exists_widePullback_in (qcqsObjects X)
    exists_pullbackCone_mem_qcqsObjects
    hU (n + 1) (fun i ↦ E.X (A i)) (fun i ↦ E.f (A i)) (fun i ↦ hmember (A i))

/-! ### The sheaf category of the small pro-étale site -/

attribute [local instance] hasSheafify_proetale

/-- Taking sections of abelian sheaves over an object is additive: addition of sections is
preserved on the nose. -/
theorem additive_sheafSections {C : Type*} [Category* C] (J : GrothendieckTopology C)
    (A : Type*) [Category* A] [Preadditive A] (U : C) :
    ((sheafSections J A).obj (op U)).Additive where
  map_add := rfl

attribute [local instance] additive_sheafSections

attribute [local instance] Stacks.Cohomology.ColimitsOfCohomology.additive_sheafΓ

/-- Abelian sheaves on the small pro-étale site form a Grothendieck abelian category relative to
the coefficient universe: the site is essentially small there, abelian groups in that universe
are Grothendieck abelian, and sheafification transports the axioms along the equivalence with a
small model. -/
theorem isGrothendieckAbelian_sheaf_proetale (X : Scheme.{u}) :
    IsGrothendieckAbelian.{max (u + 1) v}
      (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{max (u + 1) v}) :=
  Sheaf.isGrothendieckAbelian_of_essentiallySmall _ _

attribute [local instance] isGrothendieckAbelian_sheaf_proetale

/-- Abelian sheaves on the small pro-étale site have enough injectives, being a Grothendieck
abelian category. -/
theorem enoughInjectives_sheaf_proetale (X : Scheme.{u}) :
    EnoughInjectives (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{max (u + 1) v}) :=
  CategoryTheory.IsGrothendieckAbelian.enoughInjectives

attribute [local instance] enoughInjectives_sheaf_proetale

/-! ### Filtered colimits and pro-étale cohomology -/

/-- **Pro-étale cohomology over a quasi-compact quasi-separated object commutes with filtered
colimits.** For every object `U` of the small pro-étale site of `X` whose underlying scheme is
quasi-compact and quasi-separated, every degree `p` and every filtered system `F` of abelian
sheaves, the canonical map from the filtered colimit of the cohomology groups over `U` to the
cohomology of the filtered colimit is an isomorphism.

This is Stacks 0739 on the small pro-étale site: the finite coverings by objects with affine
underlying scheme are cofinal among the coverings of such a `U`, and their iterated fibre
products are again quasi-compact and quasi-separated. -/
theorem isIso_colimit_post_rightDerived_sheafSections_proetale (p : ℕ) (U : X.ProEt)
    (hU : U ∈ qcqsObjects X) {I : Type (max (u + 1) v)} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{max (u + 1) v}) :
    IsIso (colimit.post F (((sheafSections (Scheme.ProEt.topology X)
      AddCommGrpCat.{max (u + 1) v}).obj (op U)).rightDerived p)) :=
  Stacks.Cohomology.isIso_colimit_post_rightDerived_sheafSections_largeCoefficients.{v, u + 1,
      u, u + 1}
    (Scheme.ProEt.topology X) (qcqsObjects X) (qcqsCovering X)
    sieve₀_mem_topology_of_mem_qcqsCovering (fun _ _ hE ↦ hE.1) exists_qcqsCovering_le p U hU F

/-- **Stacks 0739 for the pro-étale cohomology of a quasi-compact quasi-separated scheme.** Let
`X` be a quasi-compact and quasi-separated scheme. For every degree `p` and every filtered
system `F` of abelian sheaves on the small pro-étale site of `X`, the canonical map

> `colim_i H^p(X_pro-étale, F_i) ⟶ H^p(X_pro-étale, colim_i F_i)`

is an isomorphism.

Pro-étale cohomology is the right derived functor of global sections, which is sections over
the final object `X ⟶ X` of the small pro-étale site; that object is quasi-compact and
quasi-separated, so this is the case `U = X` of
`AlgebraicGeometry.ProEtale.isIso_colimit_post_rightDerived_sheafSections_proetale`. -/
theorem isIso_colimit_post_rightDerived_Γ_proetale (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] (p : ℕ)
    {I : Type (max (u + 1) v)} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{max (u + 1) v}) :
    IsIso (colimit.post F ((Sheaf.Γ (Scheme.ProEt.topology X)
      AddCommGrpCat.{max (u + 1) v}).rightDerived p)) := by
  let : MorphismProperty.ContainsIdentities @WeaklyEtale := ⟨fun _ ↦ inferInstance⟩
  have hT : IsTerminal (Scheme.ProEt.mk (𝟙 X)) := MorphismProperty.Over.mkIdTerminal _ _
  have := isIso_colimit_post_rightDerived_sheafSections_proetale.{v} p
    (Scheme.ProEt.mk (𝟙 X)) (proEtMkId_mem_qcqsObjects X) F
  exact Stacks.Cohomology.isIso_colimit_post_of_natIso F _ _
    (Stacks.Cohomology.CompositeRightDerived.rightDerivedNatIso
      (Sheaf.ΓNatIsoSheafSections (Scheme.ProEt.topology X)
        AddCommGrpCat.{max (u + 1) v} hT) p).symm

end AlgebraicGeometry.ProEtale

end
