module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleOpenClosedTriangle
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModulesCurves.ClosedFibreSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModulesCurves.DenseComplementFiniteClosedPoints
import StacksCore.Tactic.StacksAttribute

/-!
# Finiteness of étale cohomology after restriction to a dense open

Let `Λ` be a Noetherian ring, let `k` be an algebraically closed field, let `X` be a separated
scheme of finite type over `k` of dimension at most one, let `ℱ` be a constructible sheaf of
`Λ`-modules on `X_étale`, and let `j : X' ⟶ X` be the inclusion of a dense open subscheme. Then
for every `q`

```
H^q_étale(X, ℱ) is a finite Λ-module  ↔  H^q_étale(X, j_!j^{-1}ℱ) is a finite Λ-module.
```

This is [Stacks, Tag 0GJE], and the proof is the source's. Density makes the complement
`Z = X \ X'` zero-dimensional, hence a finite set of closed points with residue field `k`, by
`Stacks.EtaleCohomology.TorsionModules.finite_compl_and_residueField_eq_of_dense_isOpenImmersion`.
The closed subscheme supported there is the disjoint union of one copy of `Spec k` per point
(`Stacks.EtaleCohomology.TorsionModules.pointsSchemeHom`); it is finite over `k`, so the
cohomology of `i_*i^{-1}ℱ` is concentrated in degree zero, where it is the product of the stalks
of `ℱ` at those points, finite because `ℱ` is constructible
(`Stacks.EtaleCohomology.TorsionModules.finite_moduleEtaleCohomology_zero_pointsDirectImage`,
`Stacks.EtaleCohomology.TorsionModules.isZero_moduleEtaleCohomology_succ_pointsDirectImage`).
The long exact cohomology sequence of the localization sequence of Tag 095L then gives the
biconditional; that last step is
`Stacks.EtaleCohomology.TorsionModules.module_finite_cohomology_iff_extensionByZero`, whose
hypotheses `h095L`, `h0` and `hpos` are all discharged here.

## Main results

* `Stacks.EtaleCohomology.TorsionModules.openClosedModuleShortComplex_shortExact` — Tag 095L
  for the functors `j_!`, `j^{-1}`, `i_*`, `i^{-1}` of
  `StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModulesCurves.RestrictToDenseOpen`.
* `Stacks.EtaleCohomology.TorsionModules.module_finite_cohomology_iff_extensionByZero_of_dense`
  — **Stacks Tag 0GJE**.

## Implementation notes

**The localization sequence.** Tag 095L for sheaves of `Λ`-modules is
`Stacks.EtaleCohomology.shortExact_etaleModuleExtensionByZero_directImage`, whose inverse image
`i^{-1}` is the abstract left adjoint of `i_*`, while the inverse image of
`Stacks.EtaleCohomology.TorsionModules.moduleInverseImage` is the explicit sheafified Kan
extension. The two are identified by uniqueness of adjoints, which carries the unit of one
adjunction to the unit of the other, and short exactness transports along the resulting
isomorphism of short complexes.

**The presentation of `X`.** `X` is an object `X` of a big étale site `B`, which is what the
constructibility theory of this repository (Tag 03RW) is indexed by, and the sheaf lives on
Mathlib's small étale site of `X.obj`, which is where étale cohomology of sheaves of `Λ`-modules
is taken; its constructibility is
`AlgebraicGeometry.IsConstructibleEtaleSiteModuleSheaf`, Tag 03RW read across
`AlgebraicGeometry.SmallEtale.sheafEquiv`. "Separated of finite type over `k`" is
`IsSeparated p`, `LocallyOfFiniteType p` and `QuasiCompact p` for the structure morphism
`p : X ⟶ Spec k`, and "of dimension at most one" is `topologicalKrullDim X ≤ 1`. Separatedness
is a hypothesis of the source and is kept; its proof does not use it.

## References

* [Stacks Project, Tag 0GJE](https://stacks.math.columbia.edu/tag/0GJE)
* [Stacks Project, Tag 095L](https://stacks.math.columbia.edu/tag/095L)
* [Stacks Project, Tag 03RW](https://stacks.math.columbia.edu/tag/03RW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u r

namespace Stacks.EtaleCohomology.TorsionModules

/-- `i_*` applied to the canonical isomorphism between the abstract and explicit `i^{-1}ℱ`. -/
private noncomputable def directImageInverseImageIso (Λ : Type r) [CommRing Λ]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (ℱ : Sheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)) :=
  (moduleDirectImage.{u, r, r} Λ i).mapIso
    ((Adjunction.leftAdjointUniq
      (Stacks.EtaleCohomology.etaleModuleInverseImageAdj.{u, r} Λ i)
      (moduleInverseImageDirectImageAdj.{u, r, r} Λ i)).app ℱ)

/-- **Stacks Tag 095L for the functors of `RestrictToDenseOpen`.** For a closed immersion `i` and
an open immersion `j` onto its complement, the counit of `j_! ⊣ j^{-1}` and the unit of
`i^{-1} ⊣ i_*` form a short exact sequence `0 → j_!j^{-1}ℱ → ℱ → i_*i^{-1}ℱ → 0`.

This is `Stacks.EtaleCohomology.shortExact_etaleModuleExtensionByZero_directImage` with its
abstract inverse image replaced by the explicit one, along the identification of the two left
adjoints of `i_*`. -/
@[sga "4 IV 14.6" "(14.6.1)", sga "4 XVII 5.1.16" "partial"]
theorem openClosedModuleShortComplex_shortExact (Λ : Type r) [CommRing Λ]
    {Z U X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j]
    (hij : Set.range j.base = (Set.range i.base)ᶜ)
    (ℱ : Sheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)) :
    ∃ hz : (moduleExtensionByZeroAdj.{u, r, r} Λ j).counit.app ℱ ≫
        (moduleInverseImageDirectImageAdj.{u, r, r} Λ i).unit.app ℱ = 0,
      (openClosedModuleShortComplex.{u, r, r} Λ i j ℱ hz).ShortExact := by
  obtain ⟨h, hS⟩ := Stacks.EtaleCohomology.shortExact_etaleModuleExtensionByZero_directImage
    Λ i j hij ℱ
  have hunit := Adjunction.unit_leftAdjointUniq_hom_app
    (Stacks.EtaleCohomology.etaleModuleInverseImageAdj.{u, r} Λ i)
    (moduleInverseImageDirectImageAdj.{u, r, r} Λ i) ℱ
  have hz : (moduleExtensionByZeroAdj.{u, r, r} Λ j).counit.app ℱ ≫
      (moduleInverseImageDirectImageAdj.{u, r, r} Λ i).unit.app ℱ = 0 := by
    have h' : (moduleExtensionByZeroAdj.{u, r, r} Λ j).counit.app ℱ ≫
        (Stacks.EtaleCohomology.etaleModuleInverseImageAdj.{u, r} Λ i).unit.app ℱ = 0 := h
    rw [← hunit, ← Category.assoc, h', zero_comp]
  refine ⟨hz, ShortComplex.shortExact_of_iso ?_ hS⟩
  refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
    (directImageInverseImageIso Λ i ℱ) ?_ ?_
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    rfl
  · simpa only [Iso.refl_hom, Category.id_comp, Functor.mapIso_hom, Iso.app_hom,
    directImageInverseImageIso] using hunit.symm

/-- **Stacks Project, Tag 0GJE.** Let `Λ` be a Noetherian ring, `k` an algebraically closed
field, `X` a separated scheme of finite type over `k` of dimension at most one, `ℱ` a
constructible sheaf of `Λ`-modules on `X_étale`, and `j : X' ⟶ X` the inclusion of a dense open
subscheme. Then `H^q_étale(X, ℱ)` is a finite `Λ`-module if and only if
`H^q_étale(X, j_!j^{-1}ℱ)` is a finite `Λ`-module.

"Separated of finite type over `k`" is `IsSeparated p`, `LocallyOfFiniteType p` and
`QuasiCompact p` for the structure morphism `p`, "of dimension at most one" is
`topologicalKrullDim X ≤ 1`, and constructibility is `IsConstructibleEtaleSiteModuleSheaf`
(Tag 03RW, read on the small étale site). The proof discharges the localization sequence
(`openClosedModuleShortComplex_shortExact`) and the cohomology of the closed part, and applies
`module_finite_cohomology_iff_extensionByZero`. -/
@[stacks 0GJE]
theorem module_finite_cohomology_iff_extensionByZero_of_dense
    (B : BigEtaleSite.{u}) (Λ : Type r) [CommRing Λ] [IsNoetherianRing Λ]
    {k : Type u} [Field k] [IsAlgClosed k]
    (X : B.Scheme) (p : X.obj ⟶ Spec (CommRingCat.of k))
    [IsSeparated p] [LocallyOfFiniteType p] [QuasiCompact p]
    (hdim : topologicalKrullDim X.obj ≤ 1)
    (ℱ : Sheaf X.obj.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ))
    (hℱ : IsConstructibleEtaleSiteModuleSheaf B X Λ ℱ)
    {X' : Scheme.{u}} (j : X' ⟶ X.obj) [IsOpenImmersion j]
    (hdense : Dense (Set.range j.base)) (q : ℕ) :
    Module.Finite Λ ((moduleEtaleCohomology.{u, r, r} Λ X.obj q).obj ℱ) ↔
      Module.Finite Λ ((moduleEtaleCohomology.{u, r, r} Λ X.obj q).obj
        ((moduleExtensionByZero.{u, r, r} Λ j).obj
          ((moduleRestriction.{u, r, r} Λ j).obj ℱ))) := by
  obtain ⟨hfin, hclosed, hres⟩ :=
    finite_compl_and_residueField_eq_of_dense_isOpenImmersion p hdim j hdense
  set T : Set X.obj := (Set.range j.base)ᶜ with hTdef
  have hcl : ∀ z : T, IsClosed ({z.1} : Set X.obj) := fun z ↦ hclosed z.1 z.2
  have e : ∀ z : T, X.obj.residueField z.1 ≅ CommRingCat.of k := fun z ↦ (hres z.1 z.2).some
  set i := pointsSchemeHom k T e with hi
  have : IsClosedImmersion i := isClosedImmersion_pointsSchemeHom k T e hfin hcl
  have hij : Set.range j.base = (Set.range i.base)ᶜ := by
    rw [hi, range_pointsSchemeHom k T e, hTdef, compl_compl]
  refine module_finite_cohomology_iff_extensionByZero.{u, r, r} Λ i j hij
    (fun i' j' _ _ h 𝒢 ↦ openClosedModuleShortComplex_shortExact Λ i' j' h 𝒢) ℱ ?_ ?_ q
  · have h0 := finite_moduleEtaleCohomology_zero_pointsDirectImage B X k T e Λ ℱ hfin hcl hℱ
    exact Module.Finite.equiv ((moduleEtaleCohomology.{u, r, r} Λ X.obj 0).mapIso
      (directImageInverseImageIso Λ i ℱ)).toLinearEquiv
  · intro m hm
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
    exact isZero_moduleEtaleCohomology_succ_pointsDirectImage B X k T e Λ hfin hcl _ n

end Stacks.EtaleCohomology.TorsionModules

end
