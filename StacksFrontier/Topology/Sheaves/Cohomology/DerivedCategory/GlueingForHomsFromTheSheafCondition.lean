module

public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Slice.RestrictionOfDerivedHoms
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.SelfExtOnACollectionOfOpens
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Glueing morphisms of the derived category out of the sheaf condition of Tag 0D66(2)

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces, let `ℬ` be a basis for the topology
of `Y`, and let `K`, `L` be objects of the unbounded derived category `D(𝒪_X)` whose restrictions
satisfy `Ext^i(K|_{f⁻¹ V}, L|_{f⁻¹ V}) = 0` for `i < 0` and every `V ∈ ℬ`.  [Stacks, Tag 0D66]
part (2) says that the rule `V ↦ Hom(K|_{f⁻¹ V}, L|_{f⁻¹ V})` is then a sheaf on `Y`.  This file
draws from that sheaf condition the conclusion it exists for: a family of morphisms
`φ_{V'} : K|_{f⁻¹ V'} ⟶ L|_{f⁻¹ V'}`, indexed by the members `V'` of `ℬ` contained in an open
`V ⊆ Y` and compatible with restriction between members, comes from one and only one morphism
`K|_{f⁻¹ V} ⟶ L|_{f⁻¹ V}`.

The sheaf is carried as a presheaf of `𝒪_Y`-modules,
`Stacks.Cohomology.UnboundedHigherDirectImage.derivedPreimageCohomologyPresheaf f
RSheafHom(K, L) 0`, whose values are identified with those groups of morphisms by
`Stacks.Cohomology.UnboundedHigherDirectImage.derivedPreimageHomPresheafValueEquiv` and whose
sheaf condition is
`Stacks.Cohomology.UnboundedHigherDirectImage.isSheaf_derivedPreimageHomPresheaf`.  The
compatibility of that value identification with the two restriction maps — the presheaf's own,
and `AlgebraicGeometry.RingedSite.restrictDerivedHom` on morphisms of the derived category — is
an explicit hypothesis `hmap` of both statements below, in the shape recorded for it in the module
documentation of
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.GlueingForHomsOverAMember`.

## The shape of the argument

Both the sheaf condition and the glueing statement are read through the value identification, so
the argument is run once and abstractly, in
`Stacks.DerivedGlueing.existsUnique_of_isBasis_of_valueEquiv`: an abelian sheaf `P` on a space, a
basis `ℬ`, a family of types `M V` with restriction maps `r`, and a bijection `P(V) ≃ M V`
carrying one restriction to the other.  Nothing about derived categories enters there.

Two points of that argument deserve naming.  The members of `ℬ` contained in `V` cover `V`
because `ℬ` is a basis, so `TopCat.Sheaf.existsUnique_gluing'` applies to them — and it is the
primed form that is wanted, since the glued section is produced over `V` itself rather than over
the supremum of the cover.  But the family `φ` is only assumed compatible for *inclusions between
members*, whereas the sheaf condition asks for agreement on the pairwise intersections `V₁ ⊓ V₂`,
which are not members.  That gap is closed by separatedness: an intersection of two members is
again covered by the members of `ℬ` inside it, on each of those the two restrictions of `φ` agree
by the family's compatibility, and `TopCat.Presheaf.IsSheaf.section_ext` identifies them.

## Off a basis, and off the whole space

A collection `ℬ` of opens of `X` that merely covers `X`, with the intersection of two members a
union of members, need not be a basis.  The coarsening of [Stacks, Tag 0D5Q], available as
`Stacks.DerivedGlueing.exists_coarsening`, produces a continuous `X → Z` whose structure sheaf is
the pushforward of `𝒪_X`, on which the images of the members of `ℬ` *are* a basis, and which
satisfies `f⁻¹(f(U)) = U` for each member `U`.  The statement above, applied there, gives the
glueing over every open of `Z`; and an open `O` of `X` which is the union of the members of `ℬ`
contained in it is the inverse image of such an open, namely of the union of the images of those
members.  `Stacks.DerivedGlueing.exists_preimage_eq_and_imageOpen_le` exhibits that open together
with the fact that it lies above the image of every member contained in `O`, which is what lets
the conclusion be read back at every member of `ℬ` below `O`: the inverse image of the coarse
open is `O`, but inverse images do not reflect inclusions, so membership of the cover has to come
from the construction rather than from the conclusion.  This is the move of
`Stacks.DerivedGlueing.subsingleton_shiftedHom_restrict_of_sSup_covered`, run for morphisms
instead of for the vanishing of negative `Ext`.

The objects `K` and `L` are global throughout: both statements restrict two objects of `D(𝒪_X)`
to an open, and neither takes objects given only over that open.

## Main results

* `Stacks.DerivedGlueing.existsUnique_of_isBasis_of_valueEquiv`: unique glueing on a basis for an
  abelian sheaf, transported along an identification of its values that carries restriction to
  restriction.
* `Stacks.DerivedGlueing.existsUnique_hom_preimageRestrict_of_isBasis_of_valueEquivMap`: a
  compatible family of morphisms between the restrictions of `K` and `L` to the inverse images of
  the members of a basis contained in `V` comes from a unique morphism over `f⁻¹ V`.
* `Stacks.DerivedGlueing.exists_preimage_eq_and_imageOpen_le`: a coarsening sees every open the
  collection covers, and sees it above the images of all the members it covers.
* `Stacks.DerivedGlueing.existsUnique_hom_restrict_of_sSup_covered_of_valueEquivMap`: the same
  conclusion for a collection of opens of `X` that covers `X` and whose pairwise intersections
  are unions of members, at every open that the collection covers.

## References

* [Stacks Project, Tag 0D66](https://stacks.math.columbia.edu/tag/0D66)
* [Stacks Project, Tag 0D5Q](https://stacks.math.columbia.edu/tag/0D5Q)
* [Stacks Project, Tag 0D67](https://stacks.math.columbia.edu/tag/0D67)
* [Stacks Project, Tag 0D68](https://stacks.math.columbia.edu/tag/0D68)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.UnboundedHigherDirectImage (preimageRestrict
  derivedPreimageCohomologyPresheaf derivedPreimageHomPresheafValueEquiv
  isSheaf_derivedPreimageHomPresheaf)
open Stacks.SheafOfModules (homSheafObject ringedSite)
open AlgebraicGeometry.RingedSite (restrictDerivedHom)

namespace Stacks.DerivedGlueing

universe v u

attribute [local instance] HasDerivedCategory.standard

/-- **Unique glueing on a basis, read through an identification of the values.** Let `P` be a
sheaf of abelian groups on a space `Z`, let `B` be a basis for its topology, and let the values
of `P` be identified with a family of types `M W` by bijections carrying the restriction maps of
`P` to a given operation `r`.  Then a family of elements `φ_W ∈ M W`, indexed by the members `W`
of `B` contained in an open `V` and compatible with `r` along inclusions between members, is
`r` applied to exactly one element of `M V`.

The index set is the members of `B` contained in `V`; they cover `V` because `B` is a basis.  The
family is only assumed compatible along inclusions of members, so its agreement on the pairwise
intersections — which are not members — is obtained from separatedness, by covering each
intersection by the members inside it. -/
@[ega "0 3.2.5" "sectionwise"]
theorem existsUnique_of_isBasis_of_valueEquiv {Z : TopCat.{u}}
    {P : TopCat.Presheaf AddCommGrpCat.{u} Z} (hsh : TopCat.Presheaf.IsSheaf P)
    {B : Set (Opens Z)} (hB : Opens.IsBasis B) {M : Opens Z → Type v}
    (e : ∀ W : Opens Z, (P.obj (op W) : Type u) ≃ M W)
    (r : ∀ {W W' : Opens Z}, W' ≤ W → M W → M W')
    (hr : ∀ {W W' : Opens Z} (h : W' ≤ W) (s : (P.obj (op W) : Type u)),
      e W' (P.map h.hom.op s) = r h (e W s))
    (V : Opens Z) (φ : ∀ W ∈ B, W ≤ V → M W)
    (hφ : ∀ (W : Opens Z) (hW : W ∈ B) (hWV : W ≤ V) (W' : Opens Z) (hW' : W' ∈ B)
      (h : W' ≤ W), r h (φ W hW hWV) = φ W' hW' (h.trans hWV)) :
    ∃! ψ : M V, ∀ (W : Opens Z) (hW : W ∈ B) (hWV : W ≤ V), r hWV ψ = φ W hW hWV := by
  classical
  have hres : ∀ {A A' A'' : Opens Z} (g₁ : A' ⟶ A) (g₂ : A'' ⟶ A') (h : A'' ≤ A)
      (x : (P.obj (op A) : Type u)),
      P.map g₂.op (P.map g₁.op x) = P.map h.hom.op x := by
    intro A A' A'' g₁ g₂ h x
    rw [← CategoryTheory.comp_apply, ← P.map_comp]
    rfl
  have key : ∀ {W T : Opens Z} (h : T ≤ W) (m : M W) (n : M T), r h m = n →
      P.map h.hom.op ((e W).symm m) = (e T).symm n := by
    rintro W T h m - rfl
    refine (e T).injective ?_
    rw [hr h, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have hcompat : TopCat.Presheaf.IsCompatible P
      (fun i : {W : Opens Z // W ∈ B ∧ W ≤ V} => i.1)
      (fun i => (e i.1).symm (φ i.1 i.2.1 i.2.2)) := by
    intro i j
    refine hsh.section_ext (U := op (i.1 ⊓ j.1)) fun x hx => ?_
    obtain ⟨T, hTB, hxT, hTij⟩ := Opens.isBasis_iff_nbhd.mp hB hx
    refine ⟨T, hTij, hxT, ?_⟩
    rw [hres _ _ (hTij.trans inf_le_left), hres _ _ (hTij.trans inf_le_right),
      key _ _ _ (hφ _ i.2.1 i.2.2 T hTB (hTij.trans inf_le_left)),
      key _ _ _ (hφ _ j.2.1 j.2.2 T hTB (hTij.trans inf_le_right))]
  have hcov : V ≤ iSup (fun i : {W : Opens Z // W ∈ B ∧ W ≤ V} => i.1) := by
    intro x hx
    obtain ⟨T, hTB, hxT, hTV⟩ := Opens.isBasis_iff_nbhd.mp hB hx
    exact Opens.mem_iSup.mpr ⟨⟨T, hTB, hTV⟩, hxT⟩
  obtain ⟨g, hg, hgu⟩ := TopCat.Sheaf.existsUnique_gluing'
    (⟨P, hsh⟩ : TopCat.Sheaf AddCommGrpCat.{u} Z)
    (fun i : {W : Opens Z // W ∈ B ∧ W ≤ V} => i.1) V (fun i => i.2.2.hom) hcov
    (fun i => (e i.1).symm (φ i.1 i.2.1 i.2.2)) hcompat
  refine ⟨e V g, fun W hW hWV => ?_, fun ψ hψ => ?_⟩
  · rw [← hr hWV, hg ⟨W, hW, hWV⟩, Equiv.apply_symm_apply]
  · have hsymm : (e V).symm ψ = g := by
      exact hgu _ fun i => key _ _ _ (hψ i.1 i.2.1 i.2.2)
    rw [← hsymm, Equiv.apply_symm_apply]

/-- **Glueing of morphisms over the inverse image of an open, on a basis** ([Stacks, Tag 0D66]
part (2)).  Let `f : X ⟶ Y` be a morphism of ringed spaces, let `ℬ` be a basis for the topology
of `Y`, and let `K`, `L` be objects of `D(𝒪_X)` with `Ext^i(K|_{f⁻¹ V}, L|_{f⁻¹ V}) = 0` for
`i < 0` and every member `V` of the basis.  A family of morphisms `K|_{f⁻¹ V'} ⟶ L|_{f⁻¹ V'}`,
indexed by the members `V'` of the basis contained in an open `V ⊆ Y` and compatible with
restriction between members,
is the restriction of a unique morphism `K|_{f⁻¹ V} ⟶ L|_{f⁻¹ V}`.

The rule `V ↦ Hom(K|_{f⁻¹ V}, L|_{f⁻¹ V})` is a sheaf by
`Stacks.Cohomology.UnboundedHigherDirectImage.isSheaf_derivedPreimageHomPresheaf`, and
`Stacks.Cohomology.UnboundedHigherDirectImage.derivedPreimageHomPresheafValueEquiv` identifies
its values with those groups of morphisms; `hmap` is the hypothesis that this identification
carries the restriction maps of the presheaf to
`AlgebraicGeometry.RingedSite.restrictDerivedHom`.  Given it, the statement is
`Stacks.DerivedGlueing.existsUnique_of_isBasis_of_valueEquiv`. -/
theorem existsUnique_hom_preimageRestrict_of_isBasis_of_valueEquivMap {X Y : RingedSpace.{u, u}}
    (f : X ⟶ Y) {B : Set (Opens Y.carrier)} (hB : Opens.IsBasis B)
    (K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (hmap : ∀ {V V' : Opens Y.carrier} (hV : V' ≤ V)
      (s : ((derivedPreimageCohomologyPresheaf f
        (Stacks.SheafOfModules.homSheafObject X.sheaf K L) 0).presheaf.obj (op V) : Type u)),
      derivedPreimageHomPresheafValueEquiv f K L V'
          (((derivedPreimageCohomologyPresheaf f
              (Stacks.SheafOfModules.homSheafObject X.sheaf K L) 0).presheaf.map hV.hom.op) s) =
        AlgebraicGeometry.RingedSite.restrictDerivedHom
          (Stacks.SheafOfModules.ringedSite X.sheaf) ((opensMap f).map hV.hom) K L
          (derivedPreimageHomPresheafValueEquiv f K L V s))
    (hExt : ∀ V ∈ B, ∀ i : ℤ, i < 0 →
      Subsingleton (ShiftedHom ((preimageRestrict f V).obj K) ((preimageRestrict f V).obj L) i))
    (V : Opens Y.carrier)
    (φ : ∀ V' ∈ B, V' ≤ V → ((preimageRestrict f V').obj K ⟶ (preimageRestrict f V').obj L))
    (hφ : ∀ (V₁ : Opens Y.carrier) (hV₁ : V₁ ∈ B) (hle₁ : V₁ ≤ V) (V₂ : Opens Y.carrier)
        (hV₂ : V₂ ∈ B) (hle : V₂ ≤ V₁),
      restrictDerivedHom (ringedSite X.sheaf) ((opensMap f).map hle.hom) K L (φ V₁ hV₁ hle₁) =
        φ V₂ hV₂ (hle.trans hle₁)) :
    ∃! ψ : (preimageRestrict f V).obj K ⟶ (preimageRestrict f V).obj L,
      ∀ (V' : Opens Y.carrier) (hV' : V' ∈ B) (hle : V' ≤ V),
        restrictDerivedHom (ringedSite X.sheaf) ((opensMap f).map hle.hom) K L ψ =
          φ V' hV' hle :=
  existsUnique_of_isBasis_of_valueEquiv
    (isSheaf_derivedPreimageHomPresheaf hB f K L hExt) hB
    (fun W => (derivedPreimageHomPresheafValueEquiv f K L W).toEquiv)
    (fun {_ _} h => restrictDerivedHom (ringedSite X.sheaf) ((opensMap f).map h.hom) K L)
    (fun {_ _} h s => hmap h s) V φ hφ

/-- **A coarsening sees every open the collection covers, above the images of the members it
covers.**  If the inverse image along `base` of the open `g W` attached to each member `W` of a
collection `ℱ` is `W` itself, then an open `O` of the source which is the union of the members of
`ℱ` contained in it is the inverse image of an open `V` of the target which moreover contains
`g W` for every member `W` contained in `O`.

This is `Stacks.DerivedGlueing.exists_preimage_eq_of_sSup_covered` with that second conclusion
added: `V` is the union of the `g W` over the members `W` contained in `O`, so each such `g W`
lies below it by `le_sSup`.  The addition is what a statement indexed by the members of a *cover*
of `V` needs, since `(Opens.map base).obj (g W) ≤ (Opens.map base).obj V` does not by itself give
`g W ≤ V`. -/
theorem exists_preimage_eq_and_imageOpen_le {T Z : TopCat.{u}} (base : T ⟶ Z)
    (ℱ : Set (Opens T)) (g : ℱ → Opens Z)
    (himage : ∀ W : ℱ, (Opens.map base).obj (g W) = W.1)
    (O : Opens T) (hO : O = sSup {W | W ∈ ℱ ∧ W ≤ O}) :
    ∃ V : Opens Z, (Opens.map base).obj V = O ∧ ∀ W : ℱ, W.1 ≤ O → g W ≤ V := by
  classical
  refine ⟨sSup {V | ∃ W : ℱ, W.1 ≤ O ∧ g W = V}, ?_, fun W hW => le_sSup ⟨W, hW, rfl⟩⟩
  refine Opens.ext (Set.ext fun x => ?_)
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · obtain ⟨V, ⟨W, hWO, rfl⟩, hxV⟩ := Opens.mem_sSup.mp hx
    have hmem : x ∈ ((Opens.map base).obj (g W) : Set T) := hxV
    rw [himage W] at hmem
    exact hWO hmem
  · rw [hO] at hx
    obtain ⟨W, hW, hxW⟩ := Opens.mem_sSup.mp hx
    refine Opens.mem_sSup.mpr ⟨g ⟨W, hW.1⟩, ⟨⟨W, hW.1⟩, hW.2, rfl⟩, ?_⟩
    have hmem : x ∈ ((Opens.map base).obj (g ⟨W, hW.1⟩) : Set T) := by
      rw [himage ⟨W, hW.1⟩]
      exact hxW
    exact hmem

/-- **Glueing of morphisms over an open that a collection covers.**  Let `(X, 𝒪_X)` be a ringed
space and let `ℬ` be a collection of open subsets covering `X` such that the intersection of two
members of `ℬ` is the union of the members of `ℬ` contained in it, and let `K`, `L` be objects of
`D(𝒪_X)` with `Ext^i(K|_U, L|_U) = 0` for `i < 0` and every `U ∈ ℬ`.  Then at every open `O` that
is the union of the members of `ℬ` contained in it, a family of morphisms `K|_W ⟶ L|_W` indexed
by those members and compatible with restriction between them is the restriction of a unique
morphism `K|_O ⟶ L|_O`.

The members of `ℬ` need not form a basis; by [Stacks, Tag 0D5Q] there is a continuous
`X → Z` whose images of the members of `ℬ` do form a basis of `Z` and satisfy `f⁻¹(f(U)) = U`,
and `Stacks.DerivedGlueing.existsUnique_hom_preimageRestrict_of_isBasis_of_valueEquivMap` applied
to it with `𝒪_Z = f_* 𝒪_X` concludes over every open of `Z`.
`Stacks.DerivedGlueing.exists_preimage_eq_and_imageOpen_le` exhibits `O` as the inverse image of
one such open lying above the images of all the members contained in `O`, so the family indexed
by the members of `ℬ` below `O` and the family indexed by the basis members below that open are
the same family.  Taking `O = ⊤` is the case of the whole space. -/
theorem existsUnique_hom_restrict_of_sSup_covered_of_valueEquivMap {X : RingedSpace.{u, u}}
    (ℬ : Set (Opens X.carrier)) (hcover : sSup ℬ = ⊤)
    (hinter : ∀ U ∈ ℬ, ∀ V ∈ ℬ, U ⊓ V = sSup {W | W ∈ ℬ ∧ W ≤ U ⊓ V})
    (K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (hmap : ∀ {Y : RingedSpace.{u, u}} (f : X ⟶ Y) {V V' : Opens Y.carrier} (hV : V' ≤ V)
      (s : ((derivedPreimageCohomologyPresheaf f
        (Stacks.SheafOfModules.homSheafObject X.sheaf K L) 0).presheaf.obj (op V) : Type u)),
      derivedPreimageHomPresheafValueEquiv f K L V'
          (((derivedPreimageCohomologyPresheaf f
              (Stacks.SheafOfModules.homSheafObject X.sheaf K L) 0).presheaf.map hV.hom.op) s) =
        AlgebraicGeometry.RingedSite.restrictDerivedHom
          (Stacks.SheafOfModules.ringedSite X.sheaf) ((opensMap f).map hV.hom) K L
          (derivedPreimageHomPresheafValueEquiv f K L V s))
    (hExt : ∀ U ∈ ℬ, ∀ i : ℤ, i < 0 → Subsingleton (ShiftedHom
      ((SheafOfModules.overFunctor.{u} (structureSheafRing X) U).mapDerivedCategory.obj K)
      ((SheafOfModules.overFunctor.{u} (structureSheafRing X) U).mapDerivedCategory.obj L) i))
    (O : Opens X.carrier) (hO : O = sSup {W | W ∈ ℬ ∧ W ≤ O})
    (φ : ∀ W ∈ ℬ, W ≤ O →
      ((SheafOfModules.overFunctor.{u} (structureSheafRing X) W).mapDerivedCategory.obj K ⟶
        (SheafOfModules.overFunctor.{u} (structureSheafRing X) W).mapDerivedCategory.obj L))
    (hφ : ∀ (W : Opens X.carrier) (hW : W ∈ ℬ) (hWO : W ≤ O) (W' : Opens X.carrier)
        (hW' : W' ∈ ℬ) (h : W' ≤ W),
      restrictDerivedHom (ringedSite X.sheaf) h.hom K L (φ W hW hWO) = φ W' hW' (h.trans hWO)) :
    ∃! ψ : (SheafOfModules.overFunctor.{u} (structureSheafRing X) O).mapDerivedCategory.obj K ⟶
        (SheafOfModules.overFunctor.{u} (structureSheafRing X) O).mapDerivedCategory.obj L,
      ∀ (W : Opens X.carrier) (hW : W ∈ ℬ) (hWO : W ≤ O),
        restrictDerivedHom (ringedSite X.sheaf) hWO.hom K L ψ = φ W hW hWO := by
  classical
  obtain ⟨Z, base, imageOpen, himage, hbasis⟩ := exists_coarsening ℬ hcover hinter
  obtain ⟨V, rfl, hVle⟩ := exists_preimage_eq_and_imageOpen_le base ℬ imageOpen himage O hO
  have hmem : ∀ V' ∈ Set.range imageOpen,
      (opensMap (pushforwardRingedMap base)).obj V' ∈ ℬ := by
    rintro - ⟨U, rfl⟩
    rw [himage U]
    exact U.2
  have hExt' : ∀ V' ∈ Set.range imageOpen, ∀ i : ℤ, i < 0 → Subsingleton (ShiftedHom
      ((preimageRestrict (pushforwardRingedMap base) V').obj K)
      ((preimageRestrict (pushforwardRingedMap base) V').obj L) i) := by
    rintro - ⟨U, rfl⟩ i hi
    have h := hExt U.1 U.2 i hi
    rwa [← himage U] at h
  obtain ⟨ψ, hψ, hψu⟩ := existsUnique_hom_preimageRestrict_of_isBasis_of_valueEquivMap
    (pushforwardRingedMap base) hbasis K L (hmap (pushforwardRingedMap base)) hExt' V
    (fun V' hV' hle => φ ((opensMap (pushforwardRingedMap base)).obj V') (hmem V' hV')
      (leOfHom ((opensMap (pushforwardRingedMap base)).map hle.hom)))
    (fun V₁ hV₁ hle₁ V₂ hV₂ hle =>
      hφ ((opensMap (pushforwardRingedMap base)).obj V₁) (hmem V₁ hV₁)
        (leOfHom ((opensMap (pushforwardRingedMap base)).map hle₁.hom))
        ((opensMap (pushforwardRingedMap base)).obj V₂) (hmem V₂ hV₂)
        (leOfHom ((opensMap (pushforwardRingedMap base)).map hle.hom)))
  refine ⟨ψ, ?_, ?_⟩
  · intro W hW hWO
    obtain ⟨V', hV'r, hV'le, rfl⟩ :
        ∃ V' : Opens Z, V' ∈ Set.range imageOpen ∧ V' ≤ V ∧
          (opensMap (pushforwardRingedMap base)).obj V' = W :=
      ⟨imageOpen ⟨W, hW⟩, ⟨⟨W, hW⟩, rfl⟩, hVle ⟨W, hW⟩ hWO, himage ⟨W, hW⟩⟩
    exact hψ V' hV'r hV'le
  · exact fun ψ' hψ' => hψu ψ' fun V' hV'r hle =>
      hψ' ((opensMap (pushforwardRingedMap base)).obj V') (hmem V' hV'r)
        (leOfHom ((opensMap (pushforwardRingedMap base)).map hle.hom))

end Stacks.DerivedGlueing

end
