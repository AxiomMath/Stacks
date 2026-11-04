module

public import StacksFrontier.AlgebraicGeometry.Perfect.KoszulCohomologyBijective
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.SelfExtOnACollectionOfOpens
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedRestrictionToOpens

/-!
# The Koszul comparison of Stacks 08DD, read on the slice site

Let `A` be a commutative ring, `f = (f₁, …, f_r)` a finite sequence in `A`, `X = Spec A` and
`U = D(f₁) ∪ ⋯ ∪ D(f_r)`. [Stacks, Tag 08DD] is proved in this development as
`Koszul.DerivedSystem.bijective_cohomologyComparison`, in the **open-subspace** model of
`𝒪_U`-modules: the comparison it is about is a map into `Hom_{D(𝒪_U)}(𝒪_U, E|_U)` with `(-)|_U`
the derived restriction `Koszul.DerivedSystem.restrictionToUnion`.

The tensor–internal-hom machinery of [Stacks, Tag 08J8] and the comparison of [Stacks, Tag 08DL]
live instead in the **slice-site** model, where `𝒪_U`-modules are modules over the structure
sheaf of the site of opens contained in `U`. This file carries the half of 08DD that the proof of
[Stacks, Tag 08EH] consumes — surjectivity, i.e. that every map `𝒪_U ⟶ E|_U` comes from a map
out of some Koszul stage — across to the slice model.

## Main results

* `Koszul.DerivedSystem.exists_factorisation_of_faithful_comparison`: the transport itself, for an
  arbitrary pair of functors out of one category compared by a faithful functor. This is where the
  change of model happens, and it is pure category theory.
* `Koszul.DerivedSystem.exists_koszulStage_factorisation`: **surjectivity of the comparison of
  [Stacks, Tag 08DC] in the open-subspace model**, in the factorisation form: a map
  `φ : 𝒪_X|_U ⟶ E|_U` with `E` of quasi-coherent cohomology is `(Iₑ ⟶ 𝒪_X)|_U` followed by
  `φ` for some stage `e` and some `ξ : Iₑ ⟶ E`.
* `Koszul.DerivedSystem.isIso_sliceRestrict_map_canonical`: the augmentation `Iₑ ⟶ 𝒪_X` becomes
  invertible under the slice-model restriction too.
* `Koszul.DerivedSystem.sliceRestrictionIsoOfUnion`: the resulting isomorphism
  `𝒪_X|_U ≅ Iₑ|_U` in the slice model.
* `Koszul.DerivedSystem.exists_koszulStage_factorisation_slice`: the same surjectivity in the
  slice model.

## Implementation notes

The factorisation form `ξ|_U = (Iₑ ⟶ 𝒪_X)|_U ≫ φ` is used in place of the form
`(𝒪_X|_U ≅ Iₑ|_U) ≫ ξ|_U = φ` that `Koszul.DerivedSystem.cohomologyComparisonHom_colimit_ι`
states. The two are equivalent, the isomorphism being inverse to the restricted augmentation, but
only the first makes sense before that invertibility is known, and only the first is preserved by
a functor. The transport lemma therefore needs no invertibility hypothesis at all.

Faithfulness of the comparison on derived categories is
`Stacks.DerivedGlueing.faithful_sliceToSubspace_mapDerivedCategory`; the two models are inverse
equivalences on modules, and that is all the transport uses. Invertibility of the restricted
augmentation is carried across separately, by reflecting it through the cohomology sheaves, where
the comparison is an equivalence of abelian categories and reflects isomorphisms on the nose.

## References

* [Stacks Project, Tag 08DD](https://stacks.math.columbia.edu/tag/08DD)
* [Stacks Project, Tag 08DC](https://stacks.math.columbia.edu/tag/08DC)
* [Stacks Project, Tag 08DL](https://stacks.math.columbia.edu/tag/08DL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open ExtensionByZeroModules Stacks.Cohomology.OpenSubspace

universe u

namespace Koszul.DerivedSystem

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### The transport -/

/-- **Transport of a factorisation statement along a faithful comparison of two functors.**

Let `R₁ : C ⥤ D₁` and `R₂ : C ⥤ D₂` be functors out of one category and let `Φ : D₁ ⥤ D₂` be
faithful with `θ : R₁ ⋙ Φ ≅ R₂`. If every morphism `R₂ O ⟶ R₂ H` is `R₂ (a i)` followed by
itself — that is, if every such morphism is `R₂ ξ` for some `ξ : I i ⟶ H` factoring the
morphism through the chosen family `a i : I i ⟶ O` — then the same holds for `R₁`.

The proof is the naturality of `θ` at `ξ` and at `a i`, and the cancellation of the isomorphism
`θ` at `H`. No invertibility of `R₁ (a i)` or `R₂ (a i)` is used. -/
theorem exists_factorisation_of_faithful_comparison
    {C : Type*} [Category C] {D₁ : Type*} [Category D₁] {D₂ : Type*} [Category D₂]
    (R₁ : C ⥤ D₁) (R₂ : C ⥤ D₂) (Φ : D₁ ⥤ D₂) [Φ.Faithful] (θ : R₁ ⋙ Φ ≅ R₂)
    {ι : Type*} (I : ι → C) (O H : C) (a : ∀ i, I i ⟶ O)
    (hsurj : ∀ ψ : R₂.obj O ⟶ R₂.obj H,
      ∃ (i : ι) (ξ : I i ⟶ H), R₂.map ξ = R₂.map (a i) ≫ ψ)
    (φ : R₁.obj O ⟶ R₁.obj H) :
    ∃ (i : ι) (ξ : I i ⟶ H), R₁.map ξ = R₁.map (a i) ≫ φ := by
  obtain ⟨i, ξ, hξ⟩ := hsurj (θ.inv.app O ≫ Φ.map φ ≫ θ.hom.app H)
  refine ⟨i, ξ, Φ.map_injective ((cancel_mono (θ.hom.app H)).1 ?_)⟩
  have hnat : Φ.map (R₁.map ξ) ≫ θ.hom.app H = θ.hom.app (I i) ≫ R₂.map ξ := θ.hom.naturality ξ
  have hnata : Φ.map (R₁.map (a i)) ≫ θ.hom.app O = θ.hom.app (I i) ≫ R₂.map (a i) :=
    θ.hom.naturality (a i)
  rw [hnat, hξ, Φ.map_comp, ← Category.assoc, ← hnata]
  simp

/-! ### Surjectivity of the comparison, in the open-subspace model -/

variable {A : CommRingCat.{u}} {r : ℕ}

/-- **Every map `𝒪_U ⟶ E|_U` factors a map out of a Koszul stage.** This is the surjectivity
half of [Stacks, Tag 08DD], as
`Koszul.DerivedSystem.bijective_cohomologyComparison` gives it, with the identification of
`H⁰(U, E)` with the morphism group removed and the restricted augmentation written out instead of
its inverse. -/
theorem exists_koszulStage_factorisation (f : Fin r → A) (E : derivedCat A)
    (hE : HasQuasicoherentCohomology A E)
    (φ : (restrictionToUnion f).obj (structureSheafObject A) ⟶ (restrictionToUnion f).obj E) :
    ∃ (e : ℕ) (ξ : (koszulDerivedSystem f).obj (op e) ⟶ E),
      (restrictionToUnion f).map ξ =
        (restrictionToUnion f).map (canonicalKoszulToStructureSheaf f e) ≫ φ := by
  have hb := bijective_cohomologyComparison f E hE
  have hsurj : Function.Surjective (cohomologyComparisonHom f E) := fun y => by
    obtain ⟨x, hx⟩ := hb.2 (sectionsEquivOfUnion f E y)
    exact ⟨x, (sectionsEquivOfUnion f E).injective hx⟩
  obtain ⟨x, hx⟩ := hsurj φ
  have : PreservesFilteredColimitsOfSize.{0, 0} (forget AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_shrink _
  obtain ⟨e, α, rfl⟩ := Concrete.colimit_exists_rep (homGroupSystem f E) x
  refine ⟨e, α, ?_⟩
  have hx2 := (cohomologyComparisonHom_colimit_ι f E e α).symm.trans hx
  rw [← hx2, ← restrictionIsoOfUnion_inv, Iso.inv_hom_id_assoc]

/-! ### The same in the slice model -/

/-- One half of an equivalence reflects isomorphisms: the unit identifies a morphism with the
image of its image, and the image of an isomorphism is one. -/
private theorem isIso_of_isIso_equivalenceFunctor_map {C D : Type*} [Category C] [Category D]
    (eq : C ≌ D) {Y Z : C} (g : Y ⟶ Z) (hg : IsIso (eq.functor.map g)) : IsIso g := by
  have := hg
  have : IsIso ((eq.functor ⋙ eq.inverse).map g) := Functor.map_isIso eq.inverse _
  exact (NatIso.isIso_map_iff eq.unitIso g).mpr inferInstance

/-- The augmentation `Iₑ ⟶ 𝒪_X` becomes invertible under restriction to `U` taken in the
slice-site model, as it does in the open-subspace model
(`Koszul.DerivedSystem.isIso_restrictionToUnion_map_canonical`): the two models agree after the
equivalence between them, and that equivalence reflects isomorphisms of cohomology sheaves. -/
theorem isIso_sliceRestrict_map_canonical (f : Fin r → A) (e : ℕ) :
    IsIso ((Stacks.SheafOfModules.derivedRestrict (Spec A).sheaf (unionOfBasicOpens f)).map
      (canonicalKoszulToStructureSheaf f e)) := by
  have h0 := (NatIso.isIso_map_iff
    (Stacks.SheafOfModules.derivedRestrictToSubspaceIso (Spec A).sheaf (unionOfBasicOpens f))
    (canonicalKoszulToStructureSheaf f e)).mpr (isIso_restrictionToUnion_map_canonical f e)
  have h : IsIso ((Stacks.SheafOfModules.sliceToSubspaceFunctor (Spec A).sheaf
      (unionOfBasicOpens f)).mapDerivedCategory.map
        ((Stacks.SheafOfModules.derivedRestrict (Spec A).sheaf (unionOfBasicOpens f)).map
          (canonicalKoszulToStructureSheaf f e))) := h0
  rw [Functor.isIso_mapDerivedCategory_map_iff] at h
  rw [DerivedCategory.isIso_iff]
  intro n
  exact isIso_of_isIso_equivalenceFunctor_map
    ((unionOfBasicOpens f).sheafOfModulesEquivOver (structureSheaf (Spec A).sheaf)) _ (h n)

/-- **The maps `Iₑ → 𝒪_X` become isomorphisms after restriction to `U`**, in the slice-site
model: this is `Koszul.DerivedSystem.restrictionIsoOfUnion` there. -/
def sliceRestrictionIsoOfUnion (f : Fin r → A) (e : ℕ) :
    (Stacks.SheafOfModules.derivedRestrict (Spec A).sheaf
        (unionOfBasicOpens f)).obj (structureSheafObject A) ≅
      (Stacks.SheafOfModules.derivedRestrict (Spec A).sheaf
        (unionOfBasicOpens f)).obj ((koszulDerivedSystem f).obj (op e)) :=
  have := isIso_sliceRestrict_map_canonical f e
  (asIso ((Stacks.SheafOfModules.derivedRestrict (Spec A).sheaf (unionOfBasicOpens f)).map
    (canonicalKoszulToStructureSheaf f e))).symm

/-- `Koszul.DerivedSystem.sliceRestrictionIsoOfUnion` is inverse to the slice-model restriction
of the augmentation `Iₑ ⟶ 𝒪_X`. -/
theorem sliceRestrictionIsoOfUnion_inv (f : Fin r → A) (e : ℕ) :
    (sliceRestrictionIsoOfUnion f e).inv =
      (Stacks.SheafOfModules.derivedRestrict (Spec A).sheaf (unionOfBasicOpens f)).map
        (canonicalKoszulToStructureSheaf f e) :=
  rfl

/-- **Every map `𝒪_U ⟶ E|_U` factors a map out of a Koszul stage**, in the slice-site model:
`Koszul.DerivedSystem.exists_koszulStage_factorisation` transported along the equivalence between
the two models of `𝒪_U`-modules. This is the form the proof of [Stacks, Tag 08EH] consumes. -/
theorem exists_koszulStage_factorisation_slice (f : Fin r → A) (E : derivedCat A)
    (hE : HasQuasicoherentCohomology A E)
    (φ : (Stacks.SheafOfModules.derivedRestrict (Spec A).sheaf
          (unionOfBasicOpens f)).obj (structureSheafObject A) ⟶
        (Stacks.SheafOfModules.derivedRestrict (Spec A).sheaf (unionOfBasicOpens f)).obj E) :
    ∃ (e : ℕ) (ξ : (koszulDerivedSystem f).obj (op e) ⟶ E),
      (Stacks.SheafOfModules.derivedRestrict (Spec A).sheaf (unionOfBasicOpens f)).map ξ =
        (Stacks.SheafOfModules.derivedRestrict (Spec A).sheaf (unionOfBasicOpens f)).map
          (canonicalKoszulToStructureSheaf f e) ≫ φ := by
  have := Stacks.DerivedGlueing.faithful_sliceToSubspace_mapDerivedCategory
    (structureSheaf (Spec A).sheaf) (unionOfBasicOpens f)
  exact exists_factorisation_of_faithful_comparison
    (Stacks.SheafOfModules.derivedRestrict (Spec A).sheaf (unionOfBasicOpens f))
    (restrictionToUnion f)
    (Stacks.SheafOfModules.sliceToSubspaceFunctor (Spec A).sheaf
      (unionOfBasicOpens f)).mapDerivedCategory
    (Stacks.SheafOfModules.derivedRestrictToSubspaceIso (Spec A).sheaf (unionOfBasicOpens f))
    (fun e : ℕ => (koszulDerivedSystem f).obj (op e)) (structureSheafObject A) E
    (fun e => canonicalKoszulToStructureSheaf f e)
    (exists_koszulStage_factorisation f E hE) φ

end Koszul.DerivedSystem

end
