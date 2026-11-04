module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreePowerSheaf

/-!
# A coproduct of presented sheaves of modules, and quasi-coherence of a coproduct

Let `(C, J)` be a site and `R` a sheaf of rings on it.  A `SheafOfModules.Presentation` of a sheaf
of modules `M` exhibits `M` as the cokernel of a morphism `free ρ ⟶ free γ` between free sheaves of
modules, and `SheafOfModules.QuasicoherentData` is such a presentation of `M.over (X i)` for a
family `X : I → C` covering the terminal object.  This file proves that both notions pass to a
coproduct, provided the covering family is the *same* one for every summand.

The mathematical point is that nothing here needs coproducts of kernels.  Mathlib's
`SheafOfModules.presentationOfIsCokernelFree` builds a presentation out of an exact sequence
`free ρ ⟶ free γ ⟶ M ⟶ 0`, and a coproduct of cokernels is the cokernel of the coproduct simply
because colimits commute with colimits.  So no exactness of coproducts — no Grothendieck axiom
AB4, no filtered-colimit hypothesis — is used or needed.

## Main definitions

* `CategoryTheory.Limits.isCokernelSigmaMap` : a coproduct of cokernel coforks is a cokernel
  cofork.  Stated for an arbitrary category with zero morphisms and the three coproducts involved.
* `SheafOfModules.Presentation.relationsHom` : the morphism `free relations.I ⟶ free generators.I`
  of a presentation, named so that `SheafOfModules.Presentation.isColimit` can be restated at a
  folded spelling, as `SheafOfModules.Presentation.isColimitRelationsHom`.
* `SheafOfModules.Presentation.coprod` : a presentation of `∐ P` out of a presentation of every
  `P n`, with `generators.I` and `relations.I` the sigma types of the pieces'.
* `SheafOfModules.QuasicoherentData.ofCoprodPresentations` : quasi-coherent data for a sheaf of
  modules `M` which, over each member `X i` of one common covering family, is a coproduct of
  presented sheaves of modules.
* `SheafOfModules.QuasicoherentData.coprod` : its specialization to `M = ∐ P` with the summands
  over `X i` the restrictions `(P n).over (X i)`.

## Main results

* `SheafOfModules.isQuasicoherent_of_coprod_presentations` : the consumer-facing form of
  `SheafOfModules.QuasicoherentData.ofCoprodPresentations`.
* `SheafOfModules.isQuasicoherent_coprod_of_coversTop` : the same for `∐ P`.
* `SheafOfModules.isQuasicoherent_coprod` : the same under `HasBinaryProducts C`, which supplies
  the comparison isomorphisms because restriction to a slice site is then a left adjoint.

## Implementation notes

**Why the comparison isomorphisms are a hypothesis and not a hidden assumption.**
`SheafOfModules.QuasicoherentData` for `∐ P` demands a presentation of `(∐ P).over (X i)`, so the
construction cannot avoid knowing that restriction to the slice site takes `∐ P` to
`∐ fun n => (P n).over (X i)`.  On a ringed space, where the site is the lattice of open subsets,
this is the familiar fact that restriction to an open is exact and commutes with direct sums.  On a
general site the only route to it in Mathlib is
`SheafOfModules.isLeftAdjoint_pushforward_of_isIso`, whose hypothesis that `Over.forget X` be a
left adjoint amounts to `HasBinaryProducts C` — the right adjoint is `Over.star X`.  Products of a
site are not part of the data of a site, so `SheafOfModules.QuasicoherentData.coprod` and
`SheafOfModules.isQuasicoherent_coprod_of_coversTop` take the comparison isomorphisms as an
explicit argument and assume no products; `SheafOfModules.isQuasicoherent_coprod` is the
convenience form that derives them, and it is the one to use on a ringed space, where
`HasBinaryProducts (TopologicalSpace.Opens X)` is intersection of opens and so costs nothing.

**The index universe is forced, not chosen**, exactly as for
`SheafOfModules.freeSigmaIso` in `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreePowerSheaf`.
A `SheafOfModules.GeneratingSections` indexes its sections by a type in the *same* universe `u` as
the sections of the sheaf of rings, so the generators of a presentation of `∐ P` — which are the
generators of the summands taken together — can only be assembled when `Σ n, (p n).generators.I`
lands in `Type u`, i.e. when the index type `ι` does.  This is not a stylistic restriction that a
more careful statement would remove: `Σ n, (p n).generators.I` is an object of
`Type (max w u)` for `ι : Type w`, and `SheafOfModules.free` accepts only `Type u`.  This is why
`SheafOfModules.QuasicoherentData.ofCoprodPresentations` is stated for summands indexed over the
site by a family `ι : I → Type u` of module-universe types, rather than for a coproduct of a family
on the site: a consumer whose coproduct is indexed by `ℕ` with `u > 0` then absorbs the reindexing
into the comparison isomorphism it must supply anyway — through `Equiv.ulift` and
`CategoryTheory.Limits.Sigma.whiskerEquiv` — instead of reindexing the sheaf of modules itself.

**No Stacks tag is claimed, deliberately**, for the same reason as in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreePowerSheaf`.  Stacks Tag 01CL asserts that the
total tensor, exterior and symmetric algebras of a quasi-coherent sheaf of modules are
quasi-coherent, and its proof opens by warning that an infinite direct sum of quasi-coherent
modules need *not* be quasi-coherent: the opens on which the summands are presented may intersect
in no neighbourhood of a point.  What rescues the lemma is the fact, established inside the proof
of Tag 01CK, that a single open neighbourhood presents `Tⁿ(F)`, `⋀ⁿ(F)` and `Symⁿ(F)`
simultaneously for every `n`.  That uniformity is the content of Tag 01CL and is not proved here;
the results below are only the formal step that it feeds, so the hypothesis of
`SheafOfModules.isQuasicoherent_coprod` is precisely what is still owed.

**What that hypothesis would be assembled from.** A presentation of `F.over (X i)` yields, by Tag
01CJ, an exact sequence `M₂ ⊗ Symᵏ(M₁) ⟶ Sym^{k+1}(M₁) ⟶ Sym^{k+1}(F.over (X i)) ⟶ 0` over the
*same* `X i` for every `k`, and that is the uniformity: Tag 01CJ is proved on this branch in both
the symmetric and the exterior case, by
`SheafOfModules.SymPresentation.epi_symDesc_app` with
`SheafOfModules.SymPresentation.symmetricPresentation_exact` and by
`SheafOfModules.ExtPresentation.epi_extDesc_app` with
`SheafOfModules.ExtPresentation.exteriorPresentation_exact`.  Turning such a sequence into a
`SheafOfModules.Presentation` needs its first two terms to be free sheaves of modules, i.e. the
sheaf-level identification of `Symᵏ (free γ)` with a free sheaf of modules on the degree-`k`
monomials.  That identification is the one input still missing:
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreePowerFree` has its sectionwise half, for
*finite* `γ` only, and records the naturality in the object of the site as owed.  Quasi-coherence
needs it for an arbitrary `γ`, since the index types of a presentation are unrestricted.

## References

* [Stacks Project, Tag 01CL](https://stacks.math.columbia.edu/tag/01CL)
* [Stacks Project, Tag 01CK](https://stacks.math.columbia.edu/tag/01CK)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public section

universe w u v₁ u₁

open CategoryTheory Limits

namespace CategoryTheory.Limits

variable {D : Type u₁} [Category.{v₁} D] [HasZeroMorphisms D] {β : Type w} {A B M : β → D}
  [HasCoproduct A] [HasCoproduct B] [HasCoproduct M] (f : ∀ b, A b ⟶ B b) (g : ∀ b, B b ⟶ M b)

/-- A coproduct of zero composites is zero. -/
lemma sigmaMap_comp_sigmaMap_eq_zero (hfg : ∀ b, f b ≫ g b = 0) :
    Sigma.map f ≫ Sigma.map g = 0 := by
  rw [Sigma.map_comp_map]
  ext b
  simp [hfg b]

/-- **A coproduct of cokernels is the cokernel of the coproduct.** This is an instance of colimits
commuting with colimits, and in particular needs no exactness of coproducts. -/
noncomputable def isCokernelSigmaMap {hfg : ∀ b, f b ≫ g b = 0}
    (h : ∀ b, IsColimit (CokernelCofork.ofπ (g b) (hfg b))) :
    IsColimit (CokernelCofork.ofπ (f := Sigma.map f) (Sigma.map g)
      (sigmaMap_comp_sigmaMap_eq_zero f g hfg)) := by
  have hc : ∀ (s : CokernelCofork (Sigma.map f)) (b : β),
      f b ≫ Sigma.ι B b ≫ Cofork.π s = 0 := fun s b => by
    rw [← Category.assoc, ← Sigma.ι_map, Category.assoc, CokernelCofork.condition, comp_zero]
  have key : ∀ (s : CokernelCofork (Sigma.map f)) (b : β),
      g b ≫ (h b).desc (CokernelCofork.ofπ (Sigma.ι B b ≫ Cofork.π s) (hc s b)) =
        Sigma.ι B b ≫ Cofork.π s := fun s b => Cofork.IsColimit.π_desc (h b)
  refine Cofork.IsColimit.mk _
    (fun s => Sigma.desc fun b => (h b).desc (CokernelCofork.ofπ _ (hc s b)))
    (fun s => Sigma.hom_ext _ _ fun b => ?_) (fun s m hm => Sigma.hom_ext _ _ fun b => ?_)
  · rw [Cofork.π_ofπ, Sigma.ι_map_assoc, Sigma.ι_desc, key s b]
  · have hm' : Sigma.map g ≫ m = Cofork.π s := by rw [← hm, Cofork.π_ofπ]
    rw [Sigma.ι_desc]
    refine Cofork.IsColimit.hom_ext (h b) ?_
    rw [Cofork.π_ofπ, key s b, ← hm', Sigma.ι_map_assoc]

end CategoryTheory.Limits

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}

/-! ### The morphism of free sheaves of modules underlying a presentation -/

section Presentation

variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {M : SheafOfModules.{u} R}

/-- The morphism `free relations.I ⟶ free generators.I` of a presentation, whose cokernel is the
presented sheaf of modules. Mathlib spells this out inside
`SheafOfModules.Presentation.isColimit`; naming it lets that statement be restated at a folded
spelling, which is what the coproduct construction below consumes. -/
noncomputable def Presentation.relationsHom (p : M.Presentation) :
    free (R := R) p.relations.I ⟶ free (R := R) p.generators.I :=
  (freeHomEquiv _).symm p.relations.s ≫ kernel.ι p.generators.π

/-- `Presentation.relationsHom` followed by the generators' projection `π` is zero. -/
@[simp]
lemma Presentation.relationsHom_comp_π (p : M.Presentation) :
    p.relationsHom ≫ p.generators.π = 0 := by
  simp [Presentation.relationsHom]

/-- `SheafOfModules.Presentation.isColimit` written with
`SheafOfModules.Presentation.relationsHom`. The two statements are definitionally equal, and the
`:=` below is where that is crossed: a goal mixing the two spellings is not type-correct at
`implicit` transparency, so no rewrite may cross it. -/
noncomputable def Presentation.isColimitRelationsHom (p : M.Presentation) :
    IsColimit (CokernelCofork.ofπ (f := p.relationsHom) p.generators.π
      p.relationsHom_comp_π) :=
  p.isColimit

end Presentation

/-! ### A coproduct of presentations -/

section Coprod

variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {ι : Type u} {P : ι → SheafOfModules.{u} R} [HasCoproduct P]

/-- **A coproduct of presented sheaves of modules is presented**, by the sigma type of the
generators and the sigma type of the relations of the summands. -/
noncomputable def Presentation.coprod (p : ∀ n, (P n).Presentation)
    [HasCoproduct fun n => free (R := R) (p n).relations.I]
    [HasCoproduct fun n => free (R := R) (p n).generators.I] :
    (∐ P).Presentation :=
  presentationOfIsCokernelFree
    ((freeSigmaIso (O := R) fun n => (p n).relations.I).inv ≫
      Limits.Sigma.map (fun n => (p n).relationsHom) ≫
        (freeSigmaIso (O := R) fun n => (p n).generators.I).hom)
    ((freeSigmaIso (O := R) fun n => (p n).generators.I).inv ≫
      Limits.Sigma.map fun n => (p n).generators.π)
    (by
      have h0 := sigmaMap_comp_sigmaMap_eq_zero (fun n => (p n).relationsHom)
        (fun n => (p n).generators.π) fun n => (p n).relationsHom_comp_π
      simp [h0])
    (by
      refine IsCokernel.ofIso _
        (isCokernelSigmaMap (fun n => (p n).relationsHom) (fun n => (p n).generators.π)
          fun n => (p n).isColimitRelationsHom) _ (freeSigmaIso _) (freeSigmaIso _)
          (Iso.refl _) ?_ ?_ <;>
        simp)

end Coprod

/-! ### Quasi-coherence of a coproduct -/

section Quasicoherent

variable [∀ X : C, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **Quasi-coherent data for a sheaf of modules which is, over one common covering family, a
coproduct of presented sheaves of modules.** The covering family `X`, and hence the index type `I`,
is shared; the generators and the relations of the resulting presentation over `X i` are the sigma
types of those of the summands `Q i n`.

The summands are allowed to be indexed differently for different `i`, and by *any* type in the
module universe, so a consumer whose coproduct is indexed by a type in a smaller universe — such as
the `ℕ` grading of a graded algebra sheaf — reindexes once, inside the isomorphism `e i`, rather
than reindexing the sheaf.

The comparison isomorphisms `e` are taken as an argument rather than derived, so that no products
of the site are assumed. See the module docstring. -/
noncomputable def QuasicoherentData.ofCoprodPresentations (M : SheafOfModules.{u} R) {I : Type w}
    (X : I → C) (hX : J.CoversTop X) {ι : I → Type u}
    (Q : ∀ i, ι i → SheafOfModules.{u} (R.over (X i))) [∀ i, HasCoproduct (Q i)]
    (p : ∀ (i : I) (n : ι i), (Q i n).Presentation)
    (e : ∀ i, (∐ Q i) ≅ M.over (X i)) :
    QuasicoherentData.{w} M where
  I := I
  X := X
  coversTop := hX
  presentation i := (Presentation.coprod (p i)).ofIsIso (e i).hom

/-- **A sheaf of modules which is, over one common covering family, a coproduct of presented
sheaves of modules is quasi-coherent.** This is the step of Stacks Tag 01CL that is not internal to
the proof of Tag 01CK: once a single covering family presents every summand, the total sheaf is
quasi-coherent. The warning that opens Tag 01CL's proof is exactly that the covering family must be
one and the same for all the summands. -/
theorem isQuasicoherent_of_coprod_presentations (M : SheafOfModules.{u} R) {I : Type w}
    (X : I → C) (hX : J.CoversTop X) {ι : I → Type u}
    (Q : ∀ i, ι i → SheafOfModules.{u} (R.over (X i))) [∀ i, HasCoproduct (Q i)]
    (p : ∀ (i : I) (n : ι i), (Q i n).Presentation)
    (e : ∀ i, (∐ Q i) ≅ M.over (X i)) :
    M.IsQuasicoherent :=
  (QuasicoherentData.ofCoprodPresentations M X hX Q p e).isQuasicoherent

variable {ι : Type u} {P : ι → SheafOfModules.{u} R} [HasCoproduct P]

/-- `SheafOfModules.QuasicoherentData.ofCoprodPresentations` for the coproduct of a family of
sheaves of modules on the site itself, with the summands over `X i` the restrictions of the `P n`.
-/
noncomputable def QuasicoherentData.coprod {I : Type w} (X : I → C) (hX : J.CoversTop X)
    (p : ∀ (i : I) (n : ι), ((P n).over (X i)).Presentation)
    (e : ∀ i, (∐ fun n => (P n).over (X i)) ≅ (∐ P).over (X i)) :
    QuasicoherentData.{w} (∐ P) :=
  QuasicoherentData.ofCoprodPresentations _ X hX (fun i n => (P n).over (X i)) p e

/-- **A coproduct of sheaves of modules presented over one common covering family is
quasi-coherent.** -/
theorem isQuasicoherent_coprod_of_coversTop {I : Type w} (X : I → C) (hX : J.CoversTop X)
    (p : ∀ (i : I) (n : ι), ((P n).over (X i)).Presentation)
    (e : ∀ i, (∐ fun n => (P n).over (X i)) ≅ (∐ P).over (X i)) :
    (∐ P).IsQuasicoherent :=
  (QuasicoherentData.coprod X hX p e).isQuasicoherent

/-- `SheafOfModules.isQuasicoherent_coprod_of_coversTop` with the comparison isomorphisms supplied:
when the site has binary products, restriction to a slice site is a left adjoint, hence preserves
the coproduct. On a ringed space the site is the lattice of opens and the hypothesis is the
existence of intersections, so nothing is assumed there. -/
theorem isQuasicoherent_coprod [HasBinaryProducts C] {I : Type w} (X : I → C)
    (hX : J.CoversTop X) (p : ∀ (i : I) (n : ι), ((P n).over (X i)).Presentation) :
    (∐ P).IsQuasicoherent := by
  refine isQuasicoherent_coprod_of_coversTop X hX p fun i => ?_
  have : (overFunctor.{u} R (X i)).IsLeftAdjoint :=
    inferInstanceAs (SheafOfModules.pushforward.{u} (𝟙 (R.over (X i)))).IsLeftAdjoint
  have : PreservesColimitsOfSize.{u, u} (overFunctor.{u} R (X i)) :=
    (Adjunction.ofIsLeftAdjoint (overFunctor.{u} R (X i))).leftAdjoint_preservesColimits
  exact (PreservesCoproduct.iso (overFunctor.{u} R (X i)) P).symm

end Quasicoherent

end SheafOfModules

end
