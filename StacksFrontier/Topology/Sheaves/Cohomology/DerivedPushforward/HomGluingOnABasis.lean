module

public import Mathlib.Algebra.Category.Grp.Limits
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Slice.RestrictionOfDerivedHoms
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ConnectivityOnABasis

/-!
# The glueing of derived morphisms over a basis

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces, let `ℬ` be a basis for the topology
of `Y` and let `K`, `L` be objects of the unbounded derived category `D(𝒪_X)` with
`Ext^i(K|_{f⁻¹ V}, L|_{f⁻¹ V}) = 0` for `i < 0` and `V ∈ ℬ`.  [Stacks, Tag 0D66] part (2) says
that the rule `V ↦ Hom(K|_{f⁻¹ V}, L|_{f⁻¹ V})` is then a sheaf on `Y`.

This file proves the corresponding glueing statement: a family of morphisms
`K|_{f⁻¹ V} ⟶ L|_{f⁻¹ V}` indexed by the members of `ℬ` contained in an open `V₀` and compatible
with restriction between them comes from a unique morphism over `V₀`, provided the identification
of the values of the Hom presheaf with the groups of morphisms carries its restriction maps to
`AlgebraicGeometry.RingedSite.restrictDerivedHom`.  It also proves that a sheaf of abelian groups
on a topological space is separated on a basis, and that a family of sections indexed by the
members of a basis contained in an open, compatible on members, glues uniquely.

## Main results

* `Stacks.Cohomology.BasisGluing.section_ext_of_isBasis` — a sheaf of abelian groups on a space
  is separated on a basis.
* `Stacks.Cohomology.BasisGluing.exists_unique_gluing_of_isBasis` — a family of sections indexed
  by the members of a basis contained in an open, compatible with restriction between members,
  glues uniquely over that open.
* `Stacks.Cohomology.BasisGluing.exists_unique_gluing_of_isBasis_equiv` — the same for a family
  of types identified with the values of the sheaf by equivalences compatible with restriction.
* `Stacks.Cohomology.UnboundedHigherDirectImage.exists_unique_restrictDerivedHom_of_isBasis` —
  the same for a family of morphisms of the derived category, granted the restriction
  compatibility of the value identification.

## References

* [Stacks Project, Tag 0D66](https://stacks.math.columbia.edu/tag/0D66)
* [Stacks Project, Tag 00VO](https://stacks.math.columbia.edu/tag/00VO)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction

/-! ### Glueing sections of a sheaf of abelian groups over a basis -/

namespace Stacks.Cohomology.BasisGluing

universe u

variable {T : TopCat.{u}} (P : TopCat.Presheaf AddCommGrpCat.{u} T)
  (hP : TopCat.Presheaf.IsSheaf P)

/-- An open set is covered by the members of a basis that it contains. -/
private theorem le_iSup_basis_members {B : Set (Opens T)} (hB : Opens.IsBasis B) (W : Opens T) :
    W ≤ ⨆ i : { U : Opens T // U ∈ B ∧ U ≤ W }, i.1 := fun x hx => by
  obtain ⟨-, ⟨V, hV_B, rfl⟩, hx_V, hV_W⟩ := hB.mem_nhds_iff.mp (W.2.mem_nhds hx)
  exact Opens.mem_iSup.mpr ⟨⟨V, hV_B, hV_W⟩, hx_V⟩

include hP in
/-- **A sheaf is separated on a basis.** Two sections of a sheaf of abelian groups over an open
`W` which agree after restriction to every member of a basis contained in `W` are equal. -/
theorem section_ext_of_isBasis {B : Set (Opens T)} (hB : Opens.IsBasis B) {W : Opens T}
    (s t : P.obj (op W))
    (h : ∀ U ∈ B, ∀ hUW : U ≤ W, P.map hUW.hom.op s = P.map hUW.hom.op t) : s = t := by
  let ι := { U : Opens T // U ∈ B ∧ U ≤ W }
  let U : ι → Opens T := fun i => i.1
  have hcover := le_iSup_basis_members hB W
  let sf : ∀ i : ι, P.obj (op (U i)) := fun i => P.map (i.2.2).hom.op s
  have hcompat : TopCat.Presheaf.IsCompatible P U sf := fun i j => by
    simp only [sf, ← CategoryTheory.comp_apply, ← P.map_comp]
    congr 1
  obtain ⟨_, -, huniq⟩ := TopCat.Sheaf.existsUnique_gluing' ⟨P, hP⟩ U W (fun i => (i.2.2).hom)
    hcover sf hcompat
  exact (huniq s fun _ => rfl).trans (huniq t fun i => (h i.1 i.2.1 i.2.2).symm).symm

include hP in
/-- **Glueing sections of a sheaf over a basis.** A family of sections of a sheaf of abelian
groups, indexed by the members of a basis contained in an open `W` and compatible with
restriction between members, comes from a unique section over `W`. -/
theorem exists_unique_gluing_of_isBasis {B : Set (Opens T)} (hB : Opens.IsBasis B) {W : Opens T}
    (sf : ∀ V ∈ B, V ≤ W → P.obj (op V))
    (hcompat : ∀ (V V' : Opens T) (hV : V ∈ B) (hV' : V' ∈ B) (hle : V' ≤ V) (hVW : V ≤ W),
      P.map hle.hom.op (sf V hV hVW) = sf V' hV' (hle.trans hVW)) :
    ∃! s : P.obj (op W), ∀ (V : Opens T) (hV : V ∈ B) (hVW : V ≤ W),
      P.map hVW.hom.op s = sf V hV hVW := by
  let ι := { V : Opens T // V ∈ B ∧ V ≤ W }
  let U : ι → Opens T := fun i => i.1
  have hcover := le_iSup_basis_members hB W
  let sfι : ∀ i : ι, P.obj (op (U i)) := fun i => sf i.1 i.2.1 i.2.2
  have hcompatι : TopCat.Presheaf.IsCompatible P U sfι := fun i j =>
    section_ext_of_isBasis P hP hB _ _ fun V hV hVij => by
      simp only [← CategoryTheory.comp_apply, ← P.map_comp]
      exact (hcompat _ V i.2.1 hV (hVij.trans inf_le_left) i.2.2).trans
        (hcompat _ V j.2.1 hV (hVij.trans inf_le_right) j.2.2).symm
  obtain ⟨g, hg, huniq⟩ := TopCat.Sheaf.existsUnique_gluing' ⟨P, hP⟩ U W (fun i => (i.2.2).hom)
    hcover sfι hcompatι
  exact ⟨g, fun V hV hVW => hg ⟨V, hV, hVW⟩,
    fun g' hg' => huniq g' fun i => hg' i.1 i.2.1 i.2.2⟩

include hP in
/-- **Glueing over a basis, transported along a family of equivalences.** Suppose the values of a
sheaf of abelian groups are identified with the members of some other family of types, by
equivalences carrying the restriction maps of the sheaf to a prescribed restriction operation.
Then that family glues over a basis exactly as the sheaf does. -/
theorem exists_unique_gluing_of_isBasis_equiv {B : Set (Opens T)} (hB : Opens.IsBasis B)
    {W : Opens T} {A : Opens T → Type*}
    (e : ∀ V : Opens T, (P.obj (op V) : Type u) ≃ A V)
    (r : ∀ V V' : Opens T, V' ≤ V → A V → A V')
    (he : ∀ (V V' : Opens T) (h : V' ≤ V) (s : (P.obj (op V) : Type u)),
      e V' (P.map h.hom.op s) = r V V' h (e V s))
    (φ : ∀ V ∈ B, V ≤ W → A V)
    (hφ : ∀ (V V' : Opens T) (hV : V ∈ B) (hV' : V' ∈ B) (hle : V' ≤ V) (hVW : V ≤ W),
      r V V' hle (φ V hV hVW) = φ V' hV' (hle.trans hVW)) :
    ∃! ψ : A W, ∀ (V : Opens T) (hV : V ∈ B) (hVW : V ≤ W), r W V hVW ψ = φ V hV hVW := by
  have hcompat : ∀ (V V' : Opens T) (hV : V ∈ B) (hV' : V' ∈ B) (hle : V' ≤ V) (hVW : V ≤ W),
      P.map hle.hom.op ((e V).symm (φ V hV hVW)) = (e V').symm (φ V' hV' (hle.trans hVW)) := by
    intro V V' hV hV' hle hVW
    refine (e V').injective ?_
    rw [he V V' hle, (e V).apply_symm_apply, (e V').apply_symm_apply]
    exact hφ V V' hV hV' hle hVW
  obtain ⟨s, hs, huniq⟩ := exists_unique_gluing_of_isBasis P hP hB
    (fun V hV hVW => (e V).symm (φ V hV hVW)) hcompat
  refine ⟨e W s, fun V hV hVW => ?_, fun ψ hψ => ?_⟩
  · rw [← he W V hVW, hs V hV hVW, (e V).apply_symm_apply]
  · refine ((e W).eq_symm_apply.mp ?_).symm
    refine (huniq ((e W).symm ψ) fun V hV hVW => ?_).symm
    refine (e V).injective ?_
    rw [he W V hVW, (e W).apply_symm_apply, (e V).apply_symm_apply]
    exact hψ V hV hVW

end Stacks.Cohomology.BasisGluing

/-! ### Glueing derived morphisms over a basis -/

namespace Stacks.Cohomology.UnboundedHigherDirectImage

universe u

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] isGrothendieckAbelian_moduleSheaves

open Stacks.SheafOfModules (homSheafObject ringedSite)

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) {B : Set (Opens Y.carrier)}
  (hB : Opens.IsBasis B) (K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))

include hB in
/-- **Glueing morphisms of the derived category over a basis** ([Stacks, Tag 0D66] part (2)).
Let `ℬ` be a basis of the topology of `Y` and let `K`, `L` be objects of `D(𝒪_X)` with
`Ext^i(K|_{f⁻¹ V}, L|_{f⁻¹ V}) = 0` for `i < 0` and `V ∈ ℬ`.  Then a family of morphisms
`K|_{f⁻¹ V} ⟶ L|_{f⁻¹ V}`, indexed by the members `V` of `ℬ` contained in an open `V₀` and
compatible with restriction between members, comes from a unique morphism
`K|_{f⁻¹ V₀} ⟶ L|_{f⁻¹ V₀}`.

The hypothesis `hmap` says that the identification `derivedPreimageHomPresheafValueEquiv` of the
values of the Hom presheaf with the groups of morphisms carries the restriction maps of the
presheaf to `AlgebraicGeometry.RingedSite.restrictDerivedHom`. -/
theorem exists_unique_restrictDerivedHom_of_isBasis
    (hExt : ∀ V ∈ B, ∀ i : ℤ, i < 0 →
      Subsingleton (ShiftedHom ((preimageRestrict f V).obj K)
        ((preimageRestrict f V).obj L) i))
    (hmap : ∀ (V V' : Opens Y.carrier) (hV : V' ≤ V)
      (s : ((derivedPreimageCohomologyPresheaf f (homSheafObject X.sheaf K L) 0).presheaf.obj
        (op V) : Type u)),
      derivedPreimageHomPresheafValueEquiv f K L V'
          (((derivedPreimageCohomologyPresheaf f (homSheafObject X.sheaf K L)
              0).presheaf.map hV.hom.op) s) =
        RingedSite.restrictDerivedHom (ringedSite X.sheaf) ((opensMap f).map hV.hom) K L
          (derivedPreimageHomPresheafValueEquiv f K L V s))
    (V₀ : Opens Y.carrier)
    (φ : ∀ V ∈ B, V ≤ V₀ → ((preimageRestrict f V).obj K ⟶ (preimageRestrict f V).obj L))
    (hφ : ∀ (V V' : Opens Y.carrier) (hV : V ∈ B) (hV' : V' ∈ B) (hle : V' ≤ V) (hVV₀ : V ≤ V₀),
      RingedSite.restrictDerivedHom (ringedSite X.sheaf) ((opensMap f).map hle.hom) K L
          (φ V hV hVV₀) = φ V' hV' (hle.trans hVV₀)) :
    ∃! ψ : (preimageRestrict f V₀).obj K ⟶ (preimageRestrict f V₀).obj L,
      ∀ (V : Opens Y.carrier) (hV : V ∈ B) (hVV₀ : V ≤ V₀),
        RingedSite.restrictDerivedHom (ringedSite X.sheaf) ((opensMap f).map hVV₀.hom) K L ψ =
          φ V hV hVV₀ :=
  Stacks.Cohomology.BasisGluing.exists_unique_gluing_of_isBasis_equiv
    (derivedPreimageCohomologyPresheaf f (homSheafObject X.sheaf K L) 0).presheaf
    (isSheaf_derivedPreimageHomPresheaf hB f K L hExt) hB
    (fun V => (derivedPreimageHomPresheafValueEquiv f K L V).toEquiv)
    (fun _ _ h => RingedSite.restrictDerivedHom (ringedSite X.sheaf) ((opensMap f).map h.hom) K L)
    (fun V V' h s => hmap V V' h s) φ hφ

end Stacks.Cohomology.UnboundedHigherDirectImage

end
