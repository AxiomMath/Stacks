module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.HomGluingInSituation0D67
public import
  StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.GlueingForHomsFromTheCoverUnconditional

/-!
# Uniqueness of a solution, assembled from the glueing of morphisms on the ringed site

Let `(X, 𝒪_X)` be a ringed space and let `S` be a system of locally given derived objects on it
(Situation 0D67, `Stacks.DerivedGlueing.LocallyGiven`).  [Stacks, Tag 0D68] has two clauses: a
solution is unique up to unique isomorphism, and the global object of a solution has no negative
self-Ext.  The second clause is
`Stacks.DerivedGlueing.Solution.subsingleton_shiftedHom_self`.  This file proves the **first**
clause at the whole space, assuming one hypothesis `hcoh`: the coherence, under the
identification `Stacks.DerivedGlueing.homEquivSlice` of morphism groups, of the restriction map
`Stacks.DerivedGlueing.restrictHomBelow` of Situation 0D67 with the restriction map
`AlgebraicGeometry.RingedSite.restrictDerivedHom` of the ringed site.

## Main results

* `Stacks.DerivedGlueing.exists_unique_hom_top_of_coherence`: the sheaf condition of
  [Stacks, Tag 0D66] part (2) in the vocabulary of Situation 0D67, at the open `⊤` — a compatible
  family of morphisms `K|_W ⟶ L|_W` over the members of a covering collection comes from a unique
  morphism `K ⟶ L`.  This is the body of `Stacks.DerivedGlueing.HasGluingForHomsOver` at `O = ⊤`.
* `Stacks.DerivedGlueing.exists_unique_solutionOverIso_of_glueOver`: the glueing argument of the
  uniqueness clause, at a single open and with the glueing at that open supplied.  This is
  `Stacks.DerivedGlueing.hasUniqueSolutionOverIso_of_hasGluingForHomsOver` with the glueing
  needed only where it is used.
* `Stacks.DerivedGlueing.exists_unique_solutionIso_of_covers_of_coherence`: **clause (a) of
  [Stacks, Tag 0D68]**, assuming `hcoh` — if the collection covers `X`, the intersection of two
  members is the union of the members it contains, and the prescribed objects have no negative
  self-Ext, then two solutions are identified by exactly one isomorphism of solutions.

## References

* [Stacks Project, Tag 0D68](https://stacks.math.columbia.edu/tag/0D68)
* [Stacks Project, Tag 0D67](https://stacks.math.columbia.edu/tag/0D67)
* [Stacks Project, Tag 0D66](https://stacks.math.columbia.edu/tag/0D66)
-/


@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open ExtensionByZeroModules RingedSpaceModuleAdjunction

namespace Stacks.DerivedGlueing

universe u

attribute [local instance 10000] HasDerivedCategory.standard

variable {X : RingedSpace.{u, u}}

/-! ### Reading a morphism between the restrictions to `O` as a morphism over `O` -/

/-- **A morphism between the restrictions of two objects over `O` to `O` itself comes from a
morphism over `O`**, namely its conjugate by the identification
`Stacks.DerivedGlueing.restrictionSelfIso` of restriction from `O` to `O` with the identity
functor. -/
theorem restrictionSelf_map_conj (S : LocallyGiven X) (O : Opens X.carrier) (hOO : O ≤ O)
    {K L : OpenDerivedCategory X O}
    (ξ : (S.restriction O O hOO).obj K ⟶ (S.restriction O O hOO).obj L) :
    (S.restriction O O hOO).map (((restrictionSelfIso S O hOO).app K).inv ≫ ξ ≫
        ((restrictionSelfIso S O hOO).app L).hom) = ξ := by
  rw [← cancel_mono (((restrictionSelfIso S O hOO).app L).hom)]
  exact (restrictionSelfIso_naturality S O hOO _).trans (Iso.hom_inv_id_assoc _ _)

/-! ### The restriction of a morphism over `⊤`, read on the site -/

/-- **The restriction to `W` of a morphism over `⊤`, read on the ringed site.** The dictionary
`Stacks.DerivedGlueing.homEquivSlice` carries the restriction to `W` of a morphism `ψ : K ⟶ L`
over `⊤` to the site's restriction, along `W ≤ ⊤`, of the morphism of global objects that `ψ`
becomes, assuming the coherence `hcoh`. -/
theorem homEquivSlice_restriction_map_of_coherence (S : LocallyGiven X)
    (hcoh : ∀ {O : Opens X.carrier} (K L : OpenDerivedCategory X O) {T W : Opens X.carrier}
      (hTW : T ≤ W) (hWO : W ≤ O)
      (φ : (S.restriction W O hWO).obj K ⟶ (S.restriction W O hWO).obj L),
      homEquivSlice S K L (hTW.trans hWO) (restrictHomBelow S hTW hWO φ) =
        RingedSite.restrictDerivedHom (Stacks.SheafOfModules.ringedSite X.sheaf) hTW.hom
          ((jShriek O (underlyingRingSheaf X)).mapDerivedCategory.obj K)
          ((jShriek O (underlyingRingSheaf X)).mapDerivedCategory.obj L)
          (homEquivSlice S K L hWO φ))
    (K L : OpenDerivedCategory X ⊤) {W : Opens X.carrier} (hW : W ≤ ⊤) (ψ : K ⟶ L) :
    homEquivSlice S K L hW ((S.restriction W ⊤ hW).map ψ) =
      RingedSite.restrictDerivedHom (Stacks.SheafOfModules.ringedSite X.sheaf) hW.hom
        ((jShriek (⊤ : Opens X.carrier) (underlyingRingSheaf X)).mapDerivedCategory.obj K)
        ((jShriek (⊤ : Opens X.carrier) (underlyingRingSheaf X)).mapDerivedCategory.obj L)
        (homEquivSlice S K L (le_rfl : (⊤ : Opens X.carrier) ≤ ⊤)
          ((S.restriction ⊤ ⊤ le_rfl).map ψ)) :=
  (congrArg (homEquivSlice S K L hW)
      (restrictHomBelow_map S hW (le_rfl : (⊤ : Opens X.carrier) ≤ ⊤) ψ).symm).trans
    (hcoh K L hW (le_rfl : (⊤ : Opens X.carrier) ≤ ⊤) ((S.restriction ⊤ ⊤ le_rfl).map ψ))

/-! ### The glueing of morphisms over `⊤` -/

/-- **The sheaf condition of [Stacks, Tag 0D66] part (2) in the vocabulary of Situation 0D67, at
the open `⊤`, assuming the coherence `hcoh`.** Let the collection cover `X` and let the
intersection of two members be the union of the members contained in it. Let `K` and `L` be objects
over `⊤` with `Ext^i(K|_W, L|_W) = 0` for `i < 0` and every member `W`. Then a family of morphisms
`K|_W ⟶ L|_W`, compatible with restriction between members, comes from a unique morphism
`K ⟶ L`. -/
theorem exists_unique_hom_top_of_coherence (S : LocallyGiven X)
    (hcoh : ∀ {O : Opens X.carrier} (K L : OpenDerivedCategory X O) {T W : Opens X.carrier}
      (hTW : T ≤ W) (hWO : W ≤ O)
      (φ : (S.restriction W O hWO).obj K ⟶ (S.restriction W O hWO).obj L),
      homEquivSlice S K L (hTW.trans hWO) (restrictHomBelow S hTW hWO φ) =
        RingedSite.restrictDerivedHom (Stacks.SheafOfModules.ringedSite X.sheaf) hTW.hom
          ((jShriek O (underlyingRingSheaf X)).mapDerivedCategory.obj K)
          ((jShriek O (underlyingRingSheaf X)).mapDerivedCategory.obj L)
          (homEquivSlice S K L hWO φ))
    (hcover : sSup S.opens = ⊤)
    (hinter : ∀ U ∈ S.opens, ∀ V ∈ S.opens, U ⊓ V = sSup {W | W ∈ S.opens ∧ W ≤ U ⊓ V})
    (K L : OpenDerivedCategory X ⊤)
    (hExt : ∀ (W : Opens X.carrier), W ∈ S.opens → ∀ hWO : W ≤ ⊤, ∀ i : ℤ, i < 0 →
      Subsingleton (ShiftedHom ((S.restriction W ⊤ hWO).obj K)
        ((S.restriction W ⊤ hWO).obj L) i))
    (φ : ∀ (W : Opens X.carrier), W ∈ S.opens → ∀ hWO : W ≤ ⊤,
      (S.restriction W ⊤ hWO).obj K ⟶ (S.restriction W ⊤ hWO).obj L)
    (hφ : ∀ (W T : Opens X.carrier) (hW : W ∈ S.opens) (hT : T ∈ S.opens) (hTW : T ≤ W)
      (hWO : W ≤ ⊤), restrictHomBelow S hTW hWO (φ W hW hWO) = φ T hT (hTW.trans hWO)) :
    ∃! ψ : K ⟶ L, ∀ (W : Opens X.carrier) (hW : W ∈ S.opens) (hWO : W ≤ ⊤),
      (S.restriction W ⊤ hWO).map ψ = φ W hW hWO := by
  obtain ⟨ψ', hψ', huniq'⟩ :=
    exists_unique_restrictDerivedHom_on_sSup_covered
      ((jShriek (⊤ : Opens X.carrier) (underlyingRingSheaf X)).mapDerivedCategory.obj K)
      ((jShriek (⊤ : Opens X.carrier) (underlyingRingSheaf X)).mapDerivedCategory.obj L)
      S.opens hcover hinter
      (fun U hU i hi => subsingleton_shiftedHom_overFunctor_jShriek S K L (le_top : U ≤ ⊤) i
        (hExt U hU le_top i hi))
      ⊤ (top_eq_sSup_covered_of_sSup_eq_top S hcover)
      (fun U hU hUO => homEquivSlice S K L hUO (φ U hU hUO))
      (fun U U' hU hU' hle hUO =>
        (hcoh K L hle hUO (φ U hU hUO)).symm.trans
          (congrArg (homEquivSlice S K L (hle.trans hUO)) (hφ U U' hU hU' hle hUO)))
  obtain ⟨ξ₀, hkey⟩ : ∃ ξ₀ : K ⟶ L,
      homEquivSlice S K L (le_rfl : (⊤ : Opens X.carrier) ≤ ⊤)
        ((S.restriction ⊤ ⊤ le_rfl).map ξ₀) = ψ' :=
    ⟨((restrictionSelfIso S ⊤ le_rfl).app K).inv ≫
        (homEquivSlice S K L (le_rfl : (⊤ : Opens X.carrier) ≤ ⊤)).symm ψ' ≫
        ((restrictionSelfIso S ⊤ le_rfl).app L).hom,
      (congrArg (homEquivSlice S K L (le_rfl : (⊤ : Opens X.carrier) ≤ ⊤))
        (restrictionSelf_map_conj S ⊤ le_rfl _)).trans (Equiv.apply_symm_apply _ _)⟩
  refine ⟨ξ₀, fun W hW hWO => ?_, fun ξ hξ => ?_⟩
  · refine (homEquivSlice S K L hWO).injective
      ((homEquivSlice_restriction_map_of_coherence S hcoh K L hWO _).trans
        (Eq.trans ?_ (hψ' W hW hWO)))
    exact congrArg (fun z =>
      RingedSite.restrictDerivedHom (Stacks.SheafOfModules.ringedSite X.sheaf) hWO.hom
        ((jShriek (⊤ : Opens X.carrier) (underlyingRingSheaf X)).mapDerivedCategory.obj K)
        ((jShriek (⊤ : Opens X.carrier) (underlyingRingSheaf X)).mapDerivedCategory.obj L) z)
      hkey
  · refine restrictionSelf_map_injective S ⊤ le_rfl
      ((homEquivSlice S K L (le_rfl : (⊤ : Opens X.carrier) ≤ ⊤)).injective
        (Eq.trans ?_ hkey.symm))
    refine huniq' _ fun W hW hWO => ?_
    exact (homEquivSlice_restriction_map_of_coherence S hcoh K L hWO ξ).symm.trans
      (congrArg (homEquivSlice S K L hWO) (hξ W hW hWO))

/-! ### The glueing argument of the uniqueness clause, at one open -/

/-- **Two solutions over `O` are identified by a unique isomorphism of solutions, granted the
glueing of morphisms at `O`.** This is
`Stacks.DerivedGlueing.hasUniqueSolutionOverIso_of_hasGluingForHomsOver` with the glueing
required only at `O` instead of at every open at once. -/
theorem exists_unique_solutionOverIso_of_glueOver (S : LocallyGiven X) {O : Opens X.carrier}
    (hglue : ∀ K L : OpenDerivedCategory X O,
      (∀ (W : Opens X.carrier), W ∈ S.opens → ∀ hWO : W ≤ O, ∀ i : ℤ, i < 0 →
        Subsingleton (ShiftedHom ((S.restriction W O hWO).obj K)
          ((S.restriction W O hWO).obj L) i)) →
      ∀ φ : ∀ (W : Opens X.carrier), W ∈ S.opens → ∀ hWO : W ≤ O,
          (S.restriction W O hWO).obj K ⟶ (S.restriction W O hWO).obj L,
        (∀ (W T : Opens X.carrier) (hW : W ∈ S.opens) (hT : T ∈ S.opens) (hTW : T ≤ W)
            (hWO : W ≤ O), restrictHomBelow S hTW hWO (φ W hW hWO) = φ T hT (hTW.trans hWO)) →
        ∃! ψ : K ⟶ L, ∀ (W : Opens X.carrier) (hW : W ∈ S.opens) (hWO : W ≤ O),
          (S.restriction W O hWO).map ψ = φ W hW hWO)
    (hExt : ∀ (U : Opens X.carrier) (hU : U ∈ S.opens), ∀ i : ℤ, i < 0 →
      Subsingleton (ShiftedHom (S.obj U hU) (S.obj U hU) i))
    (A B : SolutionOver S O) :
    ∃! φ : A.obj ≅ B.obj, A.IsCompatibleHom B φ.hom := by
  have hExt' : ∀ (C D : SolutionOver S O) (W : Opens X.carrier) (hW : W ∈ S.opens)
      (hWO : W ≤ O), ∀ i : ℤ, i < 0 →
      Subsingleton (ShiftedHom ((S.restriction W O hWO).obj C.obj)
        ((S.restriction W O hWO).obj D.obj) i) := fun C D W hW hWO i hi =>
    subsingleton_shiftedHom_of_iso (C.rho W hW hWO) (D.rho W hW hWO) i (hExt W hW i hi)
  have hcomp : ∀ C D : SolutionOver S O, ∃! ψ : C.obj ⟶ D.obj,
      ∀ (W : Opens X.carrier) (hW : W ∈ S.opens) (hWO : W ≤ O),
        (S.restriction W O hWO).map ψ = C.compHom D W hW hWO := fun C D =>
    hglue C.obj D.obj (hExt' C D) (C.compHom D)
      fun W T hW hT hTW hWO => C.restrictHomBelow_compHom D hW hT hTW hWO
  obtain ⟨Φ, hΦ, -⟩ := hcomp A B
  obtain ⟨Ψ, hΨ, -⟩ := hcomp B A
  have hone : ∀ (C : SolutionOver S O) (ξ : C.obj ⟶ C.obj),
      (∀ (W : Opens X.carrier) (hW : W ∈ S.opens) (hWO : W ≤ O),
        (S.restriction W O hWO).map ξ = 𝟙 ((S.restriction W O hWO).obj C.obj)) →
      ξ = 𝟙 C.obj := by
    intro C ξ hξ
    exact (hglue C.obj C.obj (hExt' C C)
      (fun W _hW hWO => 𝟙 ((S.restriction W O hWO).obj C.obj))
      fun _W _T _hW _hT hTW hWO => restrictHomBelow_id S hTW hWO).unique hξ
      fun W _hW _hWO => CategoryTheory.Functor.map_id _ _
  have hΦΨ : Φ ≫ Ψ = 𝟙 A.obj := by
    refine hone A _ fun W hW hWO => ?_
    rw [Functor.map_comp, hΦ W hW hWO, hΨ W hW hWO, SolutionOver.compHom_comp_compHom]
  have hΨΦ : Ψ ≫ Φ = 𝟙 B.obj := by
    refine hone B _ fun W hW hWO => ?_
    rw [Functor.map_comp, hΨ W hW hWO, hΦ W hW hWO, SolutionOver.compHom_comp_compHom]
  refine ⟨⟨Φ, Ψ, hΦΨ, hΨΦ⟩, fun W hW hWO => ?_, fun θ hθ => ?_⟩
  · rw [hΦ W hW hWO, SolutionOver.compHom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · refine Iso.ext ((hcomp A B).unique ?_ hΦ)
    intro W hW hWO
    rw [SolutionOver.compHom, ← hθ W hW hWO, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-! ### Clause (a) of Tag 0D68 -/

/-- **Clause (a) of [Stacks, Tag 0D68], assuming the coherence `hcoh`.** In Situation 0D67,
assume that the members of the collection cover `X`, that the intersection of two members is the
union of the members contained in it, and that the prescribed objects have no negative self-Ext —
hypotheses (1) and (2) of the tag.  Then any two solutions are identified by exactly one
isomorphism of solutions, that is, a solution is unique up to unique isomorphism.

The conclusion `Stacks.DerivedGlueing.Solution.IsCompatibleHom A B ψ.hom` is by definition
`∀ (U : Opens X.carrier) (hU : U ∈ S.opens), (S.restriction U ⊤ le_top).map ψ.hom ≫
(B.rho U hU).hom = (A.rho U hU).hom`, which is the clause as the source states it.

The coherence `hcoh` holds (`Stacks.DerivedGlueing.restrictHomBelow_eq_restrictDerivedHom_forall`),
and the clause without it is
`Stacks.DerivedGlueing.exists_unique_solutionIso_of_covers_unconditional`. -/
theorem exists_unique_solutionIso_of_covers_of_coherence (S : LocallyGiven X)
    (hcoh : ∀ {O : Opens X.carrier} (K L : OpenDerivedCategory X O) {T W : Opens X.carrier}
      (hTW : T ≤ W) (hWO : W ≤ O)
      (φ : (S.restriction W O hWO).obj K ⟶ (S.restriction W O hWO).obj L),
      homEquivSlice S K L (hTW.trans hWO) (restrictHomBelow S hTW hWO φ) =
        RingedSite.restrictDerivedHom (Stacks.SheafOfModules.ringedSite X.sheaf) hTW.hom
          ((jShriek O (underlyingRingSheaf X)).mapDerivedCategory.obj K)
          ((jShriek O (underlyingRingSheaf X)).mapDerivedCategory.obj L)
          (homEquivSlice S K L hWO φ))
    (hcover : sSup S.opens = ⊤)
    (hinter : ∀ U ∈ S.opens, ∀ V ∈ S.opens, U ⊓ V = sSup {W | W ∈ S.opens ∧ W ≤ U ⊓ V})
    (hExt : ∀ (U : Opens X.carrier) (hU : U ∈ S.opens), ∀ i : ℤ, i < 0 →
      Subsingleton (ShiftedHom (S.obj U hU) (S.obj U hU) i))
    (A B : Solution S) :
    ∃! ψ : A.obj ≅ B.obj, A.IsCompatibleHom B ψ.hom := by
  obtain ⟨ψ, hψ, hψuniq⟩ :=
    exists_unique_solutionOverIso_of_glueOver S
      (fun K L hExtKL φ hφ =>
        exists_unique_hom_top_of_coherence S hcoh hcover hinter K L hExtKL φ hφ)
      hExt A.toSolutionOver B.toSolutionOver
  exact ⟨ψ, Solution.isCompatibleHom_of_toSolutionOver hψ,
    fun θ hθ => hψuniq θ (Solution.isCompatibleHom_toSolutionOver hθ)⟩

end Stacks.DerivedGlueing

end
