module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.GlueingForHomsFromTheCoverUnconditional
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.HomGluingOverACoveringCollection

/-!
# The glueing of derived morphisms over a subcollection of a covering collection

Let `(X, 𝒪_X)` be a ringed space, let `ℬ` be a collection of open subsets covering `X` such that
the intersection of two members is the union of the members contained in it, and let `K`, `L` be
objects of `D(𝒪_X)` with `Ext^i(K|_U, L|_U) = 0` for `i < 0` and `U ∈ ℬ`.
`Stacks.DerivedGlueing.exists_unique_restrictDerivedHom_on_sSup_covered` glues a family of
morphisms indexed by the members of `ℬ` contained in an open `O` which is the union of those
members.

The glueing statements of Situation [Stacks, Tag 0D67] also need that conclusion for a family
indexed by the members of a *subcollection* `𝒟 ⊆ ℬ`, at an open that `𝒟` covers — the
subcollection of the members contained in one of two opens, which is the indexing the two-open
case of [Stacks, Tag 0D6A] reads the uniqueness clause of [Stacks, Tag 0D68] at.  That
subcollection does not cover `X`, so the covering statement does not apply to it directly, and
the coarsening of [Stacks, Tag 0D5Q] is not available for it either: the coarsening needs the
collection it is built from to cover.

The content of this file is that no second coarsening is needed.  Coarsen `ℬ`, which does cover,
and read the subcollection inside the coarse space: the opens attached to the members of `𝒟`
are then *not* a basis of the coarse space, but a sheaf glues over any family of opens whose
pairwise intersections are covered by members of the family, basis or not.  So the basis is used
only where it is genuinely needed — to know that the Hom presheaf of [Stacks, Tag 0D66] part (2)
is a sheaf — and the indexing family is free.

## Main results

* `Stacks.Cohomology.BasisGluing.section_ext_of_sSup_covered` — a sheaf of abelian groups is
  separated with respect to any family of opens, at an open that the family covers.
* `Stacks.Cohomology.BasisGluing.exists_unique_gluing_of_sSup_covered` and
  `Stacks.Cohomology.BasisGluing.exists_unique_gluing_of_sSup_covered_equiv` — glueing of
  sections over such a family.  Both strictly generalize their partners
  `Stacks.Cohomology.BasisGluing.exists_unique_gluing_of_isBasis` and
  `Stacks.Cohomology.BasisGluing.exists_unique_gluing_of_isBasis_equiv`: a basis satisfies the
  two hypotheses at every open.
* `Stacks.Cohomology.UnboundedHigherDirectImage.exists_unique_restrictDerivedHom_on_subfamily` —
  [Stacks, Tag 0D66] part (2) with the *sheaf* taken on a basis and the *indexing family* taken
  arbitrary.
* `Stacks.DerivedGlueing.exists_unique_restrictDerivedHom_on_subcollection` — the glueing of
  morphisms over a subcollection of a covering collection, at any open the subcollection covers.

## The hypothesis on the subcollection

`exists_unique_restrictDerivedHom_on_subcollection` asks that `𝒟` be *downward closed* in `ℬ`:
a member of `ℬ` contained in a member of `𝒟` belongs to `𝒟`.  That is what carries the covering
of the pairwise intersections of members of `𝒟` from `X` up to the coarse space, where only the
members of `ℬ` are visible through the basis.  The subcollection the two-open case uses,
`Stacks.DerivedGlueing.opensBelowPair`, is downward closed, and so is `ℬ` itself, so the
covering case is the instance `𝒟 = ℬ`.

Without it the statement is still true — the map to the coarse space is a quotient map, so
inverse image is injective on opens — but that is not visible through
`Stacks.DerivedGlueing.exists_coarsening`, which exposes only the inverse images of the
distinguished opens and the basis property.

## What this does *not* give, and what is still owed

The *indexing* of the family is now free of the covering collection.  The negative-`Ext`
hypothesis is not: `exists_unique_restrictDerivedHom_on_subcollection` still asks for
`Ext^i(K|_U, L|_U) = 0` at every member `U` of `ℬ`, because that is what makes the Hom presheaf
of [Stacks, Tag 0D66] part (2) a sheaf on the *whole* coarse space, and the sheaf condition is
used — at opens below the one being glued over, but a sheaf is all this development has.

So this file does **not** by itself give
`Stacks.DerivedGlueing.HasGluingForHomsAt S O` at a proper open `O`, and therefore does not
give `Stacks.DerivedGlueing.HasGluingForHomsOver`,
`Stacks.DerivedGlueing.HasUniqueSolutionOverIso`, or the existence half of
[Stacks, Tag 0D6A].  Those statements quantify over objects given only over `O`, and supply the
vanishing only at the members *below* `O`; the extension by zero of such an object along `O` has
`Ext^i(K|_U, L|_U) = Ext^i(K|_{U ⊓ O}, L|_{U ⊓ O})` at a member `U` not contained in `O`, and
`U ⊓ O` is a union of members below `O` but is not itself a member.  What is owed is therefore

```
theorem subsingleton_shiftedHom_restrict_on_subcollection (S : LocallyGiven X)
    (𝒟 : Set (Opens X.carrier)) (h𝒟 : 𝒟 ⊆ S.opens) (O : Opens X.carrier)
    (hO : O = sSup {W | W ∈ 𝒟 ∧ W ≤ O})
    (hinter : ∀ U ∈ 𝒟, ∀ V ∈ 𝒟, U ⊓ V = sSup {W | W ∈ 𝒟 ∧ W ≤ U ⊓ V})
    (K L : OpenDerivedCategory X O)
    (hExt : ∀ W ∈ 𝒟, ∀ hWO : W ≤ O, ∀ i : ℤ, i < 0 →
      Subsingleton (ShiftedHom ((S.restriction W O hWO).obj K)
        ((S.restriction W O hWO).obj L) i))
    (P : Opens X.carrier) (hPO : P ≤ O) (hP : P = sSup {W | W ∈ 𝒟 ∧ W ≤ P})
    (i : ℤ) (hi : i < 0) :
    Subsingleton (ShiftedHom ((S.restriction P O hPO).obj K)
      ((S.restriction P O hPO).obj L) i)
```

— that is, [Stacks, Tag 0D66] part (1) with the collection covering only `O` instead of the
whole of `X`.  It is the vanishing clause of [Stacks, Tag 0D68] on the ringed space `O`, which
is how the source itself uses it: the proof of [Stacks, Tag 0D6A] applies
[Stacks, Tag 0D68] "on the ringed space `U`" for a member `U`, and in the inductive step it
appeals to it again to see that the enlarged collection `ℬ ∪ {X'}` still satisfies hypothesis
(3).  The coarsening route cannot supply it: the coarse space of a collection covering only `O`
has a point outside the image of `O` whose only neighbourhood is the whole coarse space, and the
stalk of the relevant cohomology sheaf there is the group whose vanishing is being asserted.

## References

* [Stacks Project, Tag 0D66](https://stacks.math.columbia.edu/tag/0D66)
* [Stacks Project, Tag 0D67](https://stacks.math.columbia.edu/tag/0D67)
* [Stacks Project, Tag 0D68](https://stacks.math.columbia.edu/tag/0D68)
* [Stacks Project, Tag 0D6A](https://stacks.math.columbia.edu/tag/0D6A)
* [Stacks Project, Tag 0D5Q](https://stacks.math.columbia.edu/tag/0D5Q)

Tags covered: none.  Everything here is a step of a proof — the indexing half of the
relativization of [Stacks, Tag 0D66] part (2) — and not a clause of any tag's statement.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open ExtensionByZeroModules RingedSpaceModuleAdjunction
open Stacks.Cohomology.UnboundedHigherDirectImage (preimageRestrict
  derivedPreimageCohomologyPresheaf derivedPreimageHomPresheafValueEquiv
  derivedPreimageHomPresheafValueEquiv_map isSheaf_derivedPreimageHomPresheaf)
open Stacks.SheafOfModules (homSheafObject ringedSite)

/-! ### Glueing sections of a sheaf over a family of opens that need not be a basis -/

namespace Stacks.Cohomology.BasisGluing

universe u

variable {T : TopCat.{u}} (P : TopCat.Presheaf AddCommGrpCat.{u} T)
  (hP : TopCat.Presheaf.IsSheaf P)

include hP in
/-- **A sheaf is separated with respect to any family of opens, at an open that family covers.**
Two sections of a sheaf of abelian groups over an open `W` which agree after restriction to every
member of a family `B` contained in `W` are equal, provided `W` is the union of those members.

This is `Stacks.Cohomology.BasisGluing.section_ext_of_isBasis` with the basis hypothesis replaced
by the one thing that statement used it for.  A basis covers every open, so this generalizes it
at every open. -/
theorem section_ext_of_sSup_covered {B : Set (Opens T)} {W : Opens T}
    (hW : W = sSup {V | V ∈ B ∧ V ≤ W}) (s t : P.obj (op W))
    (h : ∀ V ∈ B, ∀ hVW : V ≤ W, P.map hVW.hom.op s = P.map hVW.hom.op t) : s = t := by
  classical
  let F : TopCat.Sheaf AddCommGrpCat.{u} T := ⟨P, hP⟩
  let ι := { V : Opens T // V ∈ B ∧ V ≤ W }
  let U : ι → Opens T := fun i => i.1
  have hcover : W ≤ iSup U := hW.le.trans (sSup_le fun V hV => le_iSup U ⟨V, hV⟩)
  let sf : ∀ i : ι, P.obj (op (U i)) := fun i => P.map (i.2.2).hom.op s
  have hcompat : TopCat.Presheaf.IsCompatible P U sf := by
    intro i j
    simp only [sf, ← CategoryTheory.comp_apply, ← P.map_comp]
    congr 1
  obtain ⟨g, -, huniq⟩ := F.existsUnique_gluing' U W (fun i => (i.2.2).hom) hcover sf hcompat
  exact (huniq s fun _ => rfl).trans (huniq t fun i => (h i.1 i.2.1 i.2.2).symm).symm

include hP in
/-- **Glueing sections of a sheaf over a family of opens that need not be a basis.** A family of
sections of a sheaf of abelian groups, indexed by the members of a family `B` of opens contained
in an open `W` and compatible with restriction between members, comes from a unique section over
`W`, provided `W` is the union of the members contained in it and the intersection of two members
is the union of the members contained in it.

The sheaf condition itself asks for compatibility on the pairwise intersections of the cover,
which are not members of `B`.  It follows from compatibility on members, because the intersection
of two members is covered by the members it contains and the sheaf is separated there,
`Stacks.Cohomology.BasisGluing.section_ext_of_sSup_covered`.

This is `Stacks.Cohomology.BasisGluing.exists_unique_gluing_of_isBasis` with the basis hypothesis
replaced by the two properties of a basis the argument uses; a basis has both at every open. -/
theorem exists_unique_gluing_of_sSup_covered {B : Set (Opens T)}
    (hinter : ∀ V ∈ B, ∀ V' ∈ B, V ⊓ V' = sSup {W | W ∈ B ∧ W ≤ V ⊓ V'})
    {W : Opens T} (hW : W = sSup {V | V ∈ B ∧ V ≤ W})
    (sf : ∀ V ∈ B, V ≤ W → P.obj (op V))
    (hcompat : ∀ (V V' : Opens T) (hV : V ∈ B) (hV' : V' ∈ B) (hle : V' ≤ V) (hVW : V ≤ W),
      P.map hle.hom.op (sf V hV hVW) = sf V' hV' (hle.trans hVW)) :
    ∃! s : P.obj (op W), ∀ (V : Opens T) (hV : V ∈ B) (hVW : V ≤ W),
      P.map hVW.hom.op s = sf V hV hVW := by
  classical
  let F : TopCat.Sheaf AddCommGrpCat.{u} T := ⟨P, hP⟩
  let ι := { V : Opens T // V ∈ B ∧ V ≤ W }
  let U : ι → Opens T := fun i => i.1
  have hcover : W ≤ iSup U := hW.le.trans (sSup_le fun V hV => le_iSup U ⟨V, hV⟩)
  let sfι : ∀ i : ι, P.obj (op (U i)) := fun i => sf i.1 i.2.1 i.2.2
  have key : ∀ (i : ι) (V : Opens T) (hV : V ∈ B) (hVi : V ≤ U i),
      P.map hVi.hom.op (sfι i) = sf V hV (hVi.trans i.2.2) := fun i V hV hVi =>
    hcompat (U i) V i.2.1 hV hVi i.2.2
  have hcompatι : TopCat.Presheaf.IsCompatible P U sfι := by
    intro i j
    refine section_ext_of_sSup_covered P hP (hinter (U i) i.2.1 (U j) j.2.1) _ _
      fun V hV hVij => ?_
    have h : ∀ (k : ι) (m : U i ⊓ U j ≤ U k),
        P.map hVij.hom.op (P.map m.hom.op (sfι k)) = sf V hV (hVij.trans (m.trans k.2.2)) := by
      intro k m
      rw [← CategoryTheory.comp_apply, ← P.map_comp]
      exact key k V hV (hVij.trans m)
    exact (h i inf_le_left).trans (h j inf_le_right).symm
  obtain ⟨g, hg, huniq⟩ := F.existsUnique_gluing' U W (fun i => (i.2.2).hom) hcover sfι hcompatι
  exact ⟨g, fun V hV hVW => hg ⟨V, hV, hVW⟩,
    fun g' hg' => huniq g' fun i => hg' i.1 i.2.1 i.2.2⟩

include hP in
/-- **Glueing over such a family, transported along a family of equivalences.** This is
`Stacks.Cohomology.BasisGluing.exists_unique_gluing_of_isBasis_equiv` with the basis hypothesis
replaced by the two properties of
`Stacks.Cohomology.BasisGluing.exists_unique_gluing_of_sSup_covered`; it is the form in which a
sheaf condition stated for a cohomology presheaf is consumed by a statement about the objects its
values are identified with. -/
theorem exists_unique_gluing_of_sSup_covered_equiv {B : Set (Opens T)}
    (hinter : ∀ V ∈ B, ∀ V' ∈ B, V ⊓ V' = sSup {W | W ∈ B ∧ W ≤ V ⊓ V'})
    {W : Opens T} (hW : W = sSup {V | V ∈ B ∧ V ≤ W}) {A : Opens T → Type*}
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
  obtain ⟨s, hs, huniq⟩ := exists_unique_gluing_of_sSup_covered P hP hinter hW
    (fun V hV hVW => (e V).symm (φ V hV hVW)) hcompat
  refine ⟨e W s, fun V hV hVW => ?_, fun ψ hψ => ?_⟩
  · rw [← he W V hVW, hs V hV hVW, (e V).apply_symm_apply]
  · refine ((e W).eq_symm_apply.mp ?_).symm
    refine (huniq ((e W).symm ψ) fun V hV hVW => ?_).symm
    refine (e V).injective ?_
    rw [he W V hVW, (e W).apply_symm_apply, (e V).apply_symm_apply]
    exact hψ V hV hVW

end Stacks.Cohomology.BasisGluing

/-! ### Glueing derived morphisms over a family that need not be a basis -/

namespace Stacks.Cohomology.UnboundedHigherDirectImage

universe u

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] isGrothendieckAbelian_moduleSheaves

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) {B : Set (Opens Y.carrier)}
  (hB : Opens.IsBasis B) (K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))

include hB in
/-- **[Stacks, Tag 0D66] part (2), the glueing of morphisms, with the indexing family free of the
basis.** Let `ℬ` be a basis of the topology of `Y` and let `K`, `L` be objects of `D(𝒪_X)` with
`Ext^i(K|_{f⁻¹ V}, L|_{f⁻¹ V}) = 0` for `i < 0` and `V ∈ ℬ`.  Let `ℬ'` be *any* family of opens
of `Y` whose pairwise intersections are unions of its members.  Then a family of morphisms
`K|_{f⁻¹ V} ⟶ L|_{f⁻¹ V}`, indexed by the members `V` of `ℬ'` contained in an open `V₀` that
they cover, and compatible with restriction between members, comes from a unique morphism over
`V₀`.

The basis is used only for the sheaf condition
`Stacks.Cohomology.UnboundedHigherDirectImage.isSheaf_derivedPreimageHomPresheaf`; the glueing
itself is `Stacks.Cohomology.BasisGluing.exists_unique_gluing_of_sSup_covered_equiv`, for which
`ℬ'` need not be a basis.  Nothing is granted: the restriction compatibility of the value
identification is
`Stacks.Cohomology.UnboundedHigherDirectImage.derivedPreimageHomPresheafValueEquiv_map`. -/
theorem exists_unique_restrictDerivedHom_on_subfamily
    (hExt : ∀ V ∈ B, ∀ i : ℤ, i < 0 →
      Subsingleton (ShiftedHom ((preimageRestrict f V).obj K)
        ((preimageRestrict f V).obj L) i))
    (B' : Set (Opens Y.carrier))
    (hinter : ∀ V ∈ B', ∀ V' ∈ B', V ⊓ V' = sSup {W | W ∈ B' ∧ W ≤ V ⊓ V'})
    (V₀ : Opens Y.carrier) (hV₀ : V₀ = sSup {V | V ∈ B' ∧ V ≤ V₀})
    (φ : ∀ V ∈ B', V ≤ V₀ → ((preimageRestrict f V).obj K ⟶ (preimageRestrict f V).obj L))
    (hφ : ∀ (V V' : Opens Y.carrier) (hV : V ∈ B') (hV' : V' ∈ B') (hle : V' ≤ V) (hVV₀ : V ≤ V₀),
      RingedSite.restrictDerivedHom (ringedSite X.sheaf) ((opensMap f).map hle.hom) K L
          (φ V hV hVV₀) = φ V' hV' (hle.trans hVV₀)) :
    ∃! ψ : (preimageRestrict f V₀).obj K ⟶ (preimageRestrict f V₀).obj L,
      ∀ (V : Opens Y.carrier) (hV : V ∈ B') (hVV₀ : V ≤ V₀),
        RingedSite.restrictDerivedHom (ringedSite X.sheaf) ((opensMap f).map hVV₀.hom) K L ψ =
          φ V hV hVV₀ :=
  Stacks.Cohomology.BasisGluing.exists_unique_gluing_of_sSup_covered_equiv
    (derivedPreimageCohomologyPresheaf f (homSheafObject X.sheaf K L) 0).presheaf
    (isSheaf_derivedPreimageHomPresheaf hB f K L hExt) hinter hV₀
    (fun V => (derivedPreimageHomPresheafValueEquiv f K L V).toEquiv)
    (fun _ _ h => RingedSite.restrictDerivedHom (ringedSite X.sheaf) ((opensMap f).map h.hom) K L)
    (fun _ _ h s => derivedPreimageHomPresheafValueEquiv_map f K L h s) φ hφ

end Stacks.Cohomology.UnboundedHigherDirectImage

/-! ### Glueing derived morphisms over a subcollection of a covering collection -/

namespace Stacks.DerivedGlueing

universe u

/-! #### The coarse opens attached to a subcollection -/

/-- **A family of opens of the coarse space whose inverse images are the members of `𝒟` sees
every open that `𝒟` covers, and sees the members of `𝒟` below it.**  This is
`Stacks.DerivedGlueing.exists_preimage_eq_of_sSup_covered'` with the collection replaced by a
subcollection, and with the further statement that the coarse open produced is itself the union
of the members of the family contained in it — which is what the glueing statement needs of the
open it glues over, and which the earlier form did not record.

Nothing about the ambient collection is involved: the only input is that the inverse image of the
open attached to a member of `𝒟` is that member. -/
theorem exists_preimage_eq_of_sSup_covered_subfamily {T Z : TopCat.{u}} (f : T ⟶ Z)
    (𝒟 : Set (Opens T)) (gD : 𝒟 → Opens Z)
    (himageD : ∀ S : 𝒟, (Opens.map f).obj (gD S) = S.1)
    (O : Opens T) (hO : O = sSup {W | W ∈ 𝒟 ∧ W ≤ O}) :
    ∃ V : Opens Z, (Opens.map f).obj V = O ∧
      V = sSup {V' | V' ∈ Set.range gD ∧ V' ≤ V} ∧ ∀ S : 𝒟, S.1 ≤ O → gD S ≤ V := by
  classical
  refine ⟨sSup {V' | ∃ S : 𝒟, S.1 ≤ O ∧ gD S = V'}, ?_, ?_,
    fun S hSO => le_sSup ⟨S, hSO, rfl⟩⟩
  · refine Opens.ext (Set.ext fun x => ⟨?_, ?_⟩)
    · intro hx
      obtain ⟨V', ⟨S, hSO, rfl⟩, hxV'⟩ := Opens.mem_sSup.mp hx
      exact hSO ((SetLike.ext_iff.mp (himageD S) x).mp hxV')
    · intro hx
      obtain ⟨W, hW, hxW⟩ := Opens.mem_sSup.mp (hO.le hx)
      exact Opens.mem_sSup.mpr ⟨gD ⟨W, hW.1⟩, ⟨⟨W, hW.1⟩, hW.2, rfl⟩,
        (SetLike.ext_iff.mp (himageD ⟨W, hW.1⟩) x).mpr hxW⟩
  · refine le_antisymm (sSup_le ?_) (sSup_le fun _ hV => hV.2)
    rintro V' ⟨S, hSO, rfl⟩
    exact le_sSup ⟨⟨S, rfl⟩, le_sSup ⟨S, hSO, rfl⟩⟩

/-- **The pairwise intersections of the coarse opens of a downward closed subcollection are
unions of them.**  Let the opens attached to the members of a collection `ℬ` be a basis of the
coarse space, with inverse images the members themselves, and let `𝒟` be a subcollection with
the property that a member of `ℬ` contained in a member of `𝒟` again has its coarse open in the
family attached to `𝒟`.  Then the family attached to `𝒟` has its pairwise intersections covered
by its own members.

This is the one place where downward closedness is used, and the reason it is needed is that the
intersection of two coarse opens is approximated from inside only by *basic* opens, that is by
the coarse opens of members of `ℬ`.  The inverse image of such a basic open is a member of `ℬ`
contained in a member of `𝒟`. -/
theorem inf_eq_sSup_range_of_isBasis {T Z : TopCat.{u}} (f : T ⟶ Z) (ℬ : Set (Opens T))
    (g : ℬ → Opens Z) (himage : ∀ W : ℬ, (Opens.map f).obj (g W) = W.1)
    (hbasis : Opens.IsBasis (Set.range g)) (𝒟 : Set (Opens T)) (gD : 𝒟 → Opens Z)
    (himageD : ∀ S : 𝒟, (Opens.map f).obj (gD S) = S.1)
    (hdown : ∀ (R : ℬ) (S : 𝒟), R.1 ≤ S.1 → g R ∈ Set.range gD) :
    ∀ V ∈ Set.range gD, ∀ V' ∈ Set.range gD,
      V ⊓ V' = sSup {W | W ∈ Set.range gD ∧ W ≤ V ⊓ V'} := by
  rintro V ⟨S, rfl⟩ V' hV'
  refine le_antisymm (fun q hq => ?_) (sSup_le fun W hW => hW.2)
  have hq_nhds : ((gD S ⊓ V' : Opens Z) : Set Z) ∈ nhds q := (gD S ⊓ V').2.mem_nhds hq
  rw [hbasis.mem_nhds_iff] at hq_nhds
  obtain ⟨-, ⟨W₀, ⟨R, rfl⟩, rfl⟩, hqW₀, hW₀le⟩ := hq_nhds
  have hW₀le' : g R ≤ gD S ⊓ V' := hW₀le
  have hRS : R.1 ≤ S.1 := (himage R).symm.trans_le
    (((Opens.map f).monotone (hW₀le'.trans inf_le_left)).trans_eq (himageD S))
  exact Opens.mem_sSup.mpr ⟨g R, ⟨hdown R S hRS, hW₀le'⟩, hqW₀⟩

section Glueing

attribute [local instance] HasDerivedCategory.standard

variable {X : RingedSpace.{u, u}}
  (K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))

/-- **The glueing of derived morphisms over a subcollection of a covering collection.**  Let `ℬ`
be a collection of open subsets covering `X` such that the intersection of two members is the
union of the members contained in it, and let `K`, `L` be objects of `D(𝒪_X)` with
`Ext^i(K|_U, L|_U) = 0` for `i < 0` and every `U ∈ ℬ`.  Let `𝒟 ⊆ ℬ` be downward closed in `ℬ`.
Then a family of morphisms `K|_U ⟶ L|_U`, indexed by the members `U` of `𝒟` contained in an open
`O` which is the union of those members, and compatible with restriction between members, comes
from a unique morphism `K|_O ⟶ L|_O`.

The case `𝒟 = ℬ` is
`Stacks.DerivedGlueing.exists_unique_restrictDerivedHom_on_sSup_covered`, and the proof is that
one with
`Stacks.Cohomology.UnboundedHigherDirectImage.exists_unique_restrictDerivedHom_on_isBasis`
replaced by
`Stacks.Cohomology.UnboundedHigherDirectImage.exists_unique_restrictDerivedHom_on_subfamily`: the
coarsening of [Stacks, Tag 0D5Q] is taken for `ℬ`, which covers, and the opens it attaches to the
members of `𝒟` are then an arbitrary family inside the coarse space rather than a basis of it.
Downward closedness of `𝒟` in `ℬ` is what carries the covering of the pairwise intersections up
to the coarse space, by `Stacks.DerivedGlueing.inf_eq_sSup_range_of_isBasis`.

Nothing is granted: no negative-`Ext` hypothesis beyond the source's, and no restriction
compatibility — the latter is
`Stacks.Cohomology.UnboundedHigherDirectImage.derivedPreimageHomPresheafValueEquiv_map`. -/
theorem exists_unique_restrictDerivedHom_on_subcollection
    (ℬ : Set (Opens X.carrier)) (hcover : sSup ℬ = ⊤)
    (hinter : ∀ U ∈ ℬ, ∀ V ∈ ℬ, U ⊓ V = sSup {W | W ∈ ℬ ∧ W ≤ U ⊓ V})
    (hExt : ∀ U ∈ ℬ, ∀ i : ℤ, i < 0 → Subsingleton (ShiftedHom
      ((SheafOfModules.overFunctor.{u} (structureSheafRing X) U).mapDerivedCategory.obj K)
      ((SheafOfModules.overFunctor.{u} (structureSheafRing X) U).mapDerivedCategory.obj L) i))
    (𝒟 : Set (Opens X.carrier)) (h𝒟 : 𝒟 ⊆ ℬ)
    (hdown : ∀ R ∈ ℬ, ∀ S ∈ 𝒟, R ≤ S → R ∈ 𝒟)
    (O : Opens X.carrier) (hO : O = sSup {W | W ∈ 𝒟 ∧ W ≤ O})
    (φ : ∀ U ∈ 𝒟, U ≤ O →
      ((SheafOfModules.overFunctor.{u} (structureSheafRing X) U).mapDerivedCategory.obj K ⟶
        (SheafOfModules.overFunctor.{u} (structureSheafRing X) U).mapDerivedCategory.obj L))
    (hφ : ∀ (U U' : Opens X.carrier) (hU : U ∈ 𝒟) (hU' : U' ∈ 𝒟) (hle : U' ≤ U) (hUO : U ≤ O),
      RingedSite.restrictDerivedHom (ringedSite X.sheaf) hle.hom K L (φ U hU hUO) =
        φ U' hU' (hle.trans hUO)) :
    ∃! ψ : (SheafOfModules.overFunctor.{u} (structureSheafRing X) O).mapDerivedCategory.obj K ⟶
        (SheafOfModules.overFunctor.{u} (structureSheafRing X) O).mapDerivedCategory.obj L,
      ∀ (U : Opens X.carrier) (hU : U ∈ 𝒟) (hUO : U ≤ O),
        RingedSite.restrictDerivedHom (ringedSite X.sheaf) hUO.hom K L ψ = φ U hU hUO := by
  classical
  obtain ⟨Z, base, imageOpen, himage, hbasis⟩ := exists_coarsening ℬ hcover hinter
  obtain ⟨gD, himageD, hdownD⟩ : ∃ gD : 𝒟 → Opens Z,
      (∀ S : 𝒟, (opensMap (pushforwardRingedMap base)).obj (gD S) = S.1) ∧
        ∀ (R : ℬ) (S : 𝒟), R.1 ≤ S.1 → imageOpen R ∈ Set.range gD :=
    ⟨fun S => imageOpen ⟨S.1, h𝒟 S.2⟩, fun S => himage ⟨S.1, h𝒟 S.2⟩,
      fun R S hRS => ⟨⟨R.1, hdown R.1 R.2 S.1 S.2 hRS⟩, rfl⟩⟩
  obtain ⟨V₀, hV₀, hV₀cov, hgDV₀⟩ :=
    exists_preimage_eq_of_sSup_covered_subfamily base 𝒟 gD himageD O hO
  have hmono : ∀ {V V' : Opens Z}, V' ≤ V →
      (opensMap (pushforwardRingedMap base)).obj V' ≤
        (opensMap (pushforwardRingedMap base)).obj V := fun h => (Opens.map _).monotone h
  have heqG : ∀ {𝒞 : Set (Opens X.carrier)} (g : 𝒞 → Opens Z),
      (∀ S : 𝒞, (opensMap (pushforwardRingedMap base)).obj (g S) = S.1) →
      ∀ (V : Opens Z) (hV : V ∈ Set.range g),
        (opensMap (pushforwardRingedMap base)).obj V = (hV.choose).1 := fun g hg V hV =>
    (congrArg (opensMap (pushforwardRingedMap base)).obj hV.choose_spec.symm).trans
      (hg hV.choose)
  have heq := heqG gD himageD
  have heqB := heqG imageOpen himage
  have hleO : ∀ (V : Opens Z) (hV : V ∈ Set.range gD), V ≤ V₀ → (hV.choose).1 ≤ O :=
    fun V hV hVV₀ => (heq V hV).symm.trans_le (hV₀ ▸ hmono hVV₀)
  have hpickle : ∀ (V V' : Opens Z) (hV : V ∈ Set.range gD) (hV' : V' ∈ Set.range gD),
      V' ≤ V → (hV'.choose).1 ≤ (hV.choose).1 :=
    fun V V' hV hV' hle => (heq V' hV').symm.trans_le ((hmono hle).trans_eq (heq V hV))
  have hExtB : ∀ V ∈ Set.range imageOpen, ∀ i : ℤ, i < 0 → Subsingleton (ShiftedHom
      ((preimageRestrict (pushforwardRingedMap base) V).obj K)
      ((preimageRestrict (pushforwardRingedMap base) V).obj L) i) := by
    intro V hV i hi
    have h := hExt (hV.choose).1 (hV.choose).2 i hi
    rwa [← heqB V hV] at h
  have hφB : ∀ (V V' : Opens Z) (hV : V ∈ Set.range gD) (hV' : V' ∈ Set.range gD) (hle : V' ≤ V)
      (hVV₀ : V ≤ V₀),
      RingedSite.restrictDerivedHom (ringedSite X.sheaf)
          ((opensMap (pushforwardRingedMap base)).map hle.hom) K L
          (homCastOpen K L (heq V hV).symm (φ (hV.choose).1 (hV.choose).2 (hleO V hV hVV₀))) =
        homCastOpen K L (heq V' hV').symm
          (φ (hV'.choose).1 (hV'.choose).2 (hleO V' hV' (hle.trans hVV₀))) := by
    intro V V' hV hV' hle hVV₀
    rw [restrictDerivedHom_homCastOpen K L (heq V hV).symm (heq V' hV').symm
      (hpickle V V' hV hV' hle).hom ((opensMap (pushforwardRingedMap base)).map hle.hom)]
    exact congrArg (homCastOpen K L (heq V' hV').symm)
      (hφ (hV.choose).1 (hV'.choose).1 (hV.choose).2 (hV'.choose).2
        (hpickle V V' hV hV' hle) (hleO V hV hVV₀))
  obtain ⟨ψ, hψ, huniq⟩ :=
    Stacks.Cohomology.UnboundedHigherDirectImage.exists_unique_restrictDerivedHom_on_subfamily
      (pushforwardRingedMap base) hbasis K L hExtB (Set.range gD)
      (inf_eq_sSup_range_of_isBasis base ℬ imageOpen himage hbasis 𝒟 gD himageD hdownD) V₀ hV₀cov
      (fun V hV hVV₀ =>
        homCastOpen K L (heq V hV).symm (φ (hV.choose).1 (hV.choose).2 (hleO V hV hVV₀))) hφB
  refine ⟨homCastOpen K L hV₀ ψ, fun U hU hUO => ?_, fun ψ' hψ' => ?_⟩
  · have hVmem : gD ⟨U, hU⟩ ∈ Set.range gD := ⟨⟨U, hU⟩, rfl⟩
    have hVV₀ : gD ⟨U, hU⟩ ≤ V₀ := hgDV₀ ⟨U, hU⟩ hUO
    have hVU : (opensMap (pushforwardRingedMap base)).obj (gD ⟨U, hU⟩) = U := himageD ⟨U, hU⟩
    exact (restrictDerivedHom_homCastOpen K L hV₀ hVU
          ((opensMap (pushforwardRingedMap base)).map hVV₀.hom) hUO.hom ψ).trans
      ((congrArg (homCastOpen K L hVU) (hψ (gD ⟨U, hU⟩) hVmem hVV₀)).trans
        ((homCastOpen_trans K L (heq (gD ⟨U, hU⟩) hVmem).symm hVU _).trans
          (homCastOpen_family K L φ _ _ _ hU hUO)))
  · have hkey : homCastOpen K L hV₀.symm ψ' = ψ := huniq _ fun V hV hVV₀ =>
      (restrictDerivedHom_homCastOpen K L hV₀.symm (heq V hV).symm
          (hleO V hV hVV₀).hom ((opensMap (pushforwardRingedMap base)).map hVV₀.hom) ψ').trans
        (congrArg (homCastOpen K L (heq V hV).symm)
          (hψ' (hV.choose).1 (hV.choose).2 (hleO V hV hVV₀)))
    exact (homCastOpen_rfl K L ψ').symm.trans
      ((homCastOpen_trans K L hV₀.symm hV₀ ψ').symm.trans (congrArg (homCastOpen K L hV₀) hkey))

end Glueing

end Stacks.DerivedGlueing

end
