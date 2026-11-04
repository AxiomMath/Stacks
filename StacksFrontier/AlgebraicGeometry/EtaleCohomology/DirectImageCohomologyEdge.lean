module
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianPairRestriction
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.RingTheory.FinitePresentation.ModuleDescent

public import Mathlib.Algebra.FiveLemma
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import StacksFrontier.Algebra.Homology.RightDerivedDelta
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericPointDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericPointDirectImageUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.RestrictionLongExactSequence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleAbelianDerivedFunctors

/-!
# The cohomology of a direct image without higher direct images

Let `i : Y ⟶ X` be a morphism of schemes and `B` an abelian sheaf on `Y_étale`. Restricting a
class of `H ^ q (X_étale, i_* B)` along `i` and applying the counit `i⁻¹ i_* B ⟶ B` gives the
*edge map*

  `H ^ q (X_étale, i_* B) ⟶ H ^ q (Y_étale, B)`,

and when the higher direct images `R ^ n i_* B` vanish for `n ≥ 1` it is bijective in every
degree. This is the degeneration of the Leray spectral sequence ([Stacks, Tag 0733]) in the case
it collapses, stated for the canonical map rather than for an abstract isomorphism.

## Main definitions

* `Stacks.EtaleCohomology.etaleCohomologyDirectImageEdge`: the edge map.

## Main results

* `Stacks.EtaleCohomology.etaleCohomologyDirectImageEdge_map`: it is natural in `B`.
* `Stacks.EtaleCohomology.etaleCohomologyDirectImageEdge_comp_extClass`: it commutes with the
  connecting maps of a short exact sequence whose direct image is short exact.
* `Stacks.EtaleCohomology.bijective_etaleCohomologyDirectImageEdge`: **it is bijective when the
  higher direct images of `B` vanish.**

## Implementation notes

The proof is dimension shifting. In degree zero the edge map is the adjunction bijection
`Hom(ℤ_X, i_* B) ≃ Hom(i⁻¹ ℤ_X, B)`, read through `i⁻¹ ℤ_X ≅ ℤ_Y`. In degree `q + 1`, embed `B`
into an injective `I` with quotient `Q`. The direct image of `0 ⟶ B ⟶ I ⟶ Q ⟶ 0` is short exact
because `R¹ i_* B = 0`, the direct image of `I` is injective because inverse image is exact, and
`Q` has no higher direct images; the edge maps form a morphism between the two long exact
sequences of `Ext`, and the five lemma, with the degree-`q` case for `I` and `Q`, concludes.

## References

* [Stacks Project, Tag 0733](https://stacks.math.columbia.edu/tag/0733)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry

universe u v w

namespace Stacks.EtaleCohomology

variable {X Y : Scheme.{u}} (i : Y ⟶ X)
  [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]

/-- **The edge map** `H ^ q (X_étale, i_* B) ⟶ H ^ q (Y_étale, B)` for `i : Y ⟶ X`: restriction
along `i` followed by the counit `i⁻¹ i_* B ⟶ B`. -/
def etaleCohomologyDirectImageEdge (B : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (q : ℕ) :
    Sheaf.H.{w} ((etaleAbelianDirectImage.{u, v} i).obj B) q →+ Sheaf.H.{w} B q :=
  (Sheaf.H.map ((etaleAbelianInverseImageDirectImageAdj.{u, v} i).counit.app B) q).comp
    (etaleCohomologyRestrictionMap.{u, v, w} i _ q)

/-- The edge map sends a class `x` to the image under the counit `i⁻¹ i_* B ⟶ B` of the
restriction of `x` along `i`. -/
theorem etaleCohomologyDirectImageEdge_apply
    (B : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (q : ℕ)
    (x : Sheaf.H.{w} ((etaleAbelianDirectImage.{u, v} i).obj B) q) :
    etaleCohomologyDirectImageEdge.{u, v, w} i B q x =
      Sheaf.H.map ((etaleAbelianInverseImageDirectImageAdj.{u, v} i).counit.app B) q
        (etaleCohomologyRestrictionMap.{u, v, w} i _ q x) :=
  rfl

/-- **The edge map is natural in the sheaf.** -/
theorem etaleCohomologyDirectImageEdge_map
    {B B' : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}} (g : B ⟶ B') (q : ℕ)
    (x : Sheaf.H.{w} ((etaleAbelianDirectImage.{u, v} i).obj B) q) :
    etaleCohomologyDirectImageEdge.{u, v, w} i B' q
        (Sheaf.H.map ((etaleAbelianDirectImage.{u, v} i).map g) q x) =
      Sheaf.H.map g q (etaleCohomologyDirectImageEdge.{u, v, w} i B q x) := by
  simp only [etaleCohomologyDirectImageEdge_apply, Sheaf.H.map_apply]
  rw [etaleCohomologyRestrictionMap_comp_mk₀.{u, v, w}, Ext.comp_assoc_of_third_deg_zero,
    Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀]
  congr 2
  exact (etaleAbelianInverseImageDirectImageAdj.{u, v} i).counit.naturality g

/-- **The edge map commutes with the connecting maps** of a short exact sequence `S` on
`Y_étale` whose direct image is again short exact. -/
theorem etaleCohomologyDirectImageEdge_comp_extClass
    {S : ShortComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})}
    (hS : S.ShortExact) (hS' : (S.map (etaleAbelianDirectImage.{u, v} i)).ShortExact)
    (q r : ℕ) (hqr : q + 1 = r)
    (x : Sheaf.H.{w} ((etaleAbelianDirectImage.{u, v} i).obj S.X₃) q) :
    etaleCohomologyDirectImageEdge.{u, v, w} i S.X₁ r (x.comp hS'.extClass hqr) =
      (etaleCohomologyDirectImageEdge.{u, v, w} i S.X₃ q x).comp hS.extClass hqr := by
  let adj := etaleAbelianInverseImageDirectImageAdj.{u, v} i
  let φ : (S.map (etaleAbelianDirectImage.{u, v} i)).map (etaleAbelianInverseImage.{u, v} i) ⟶
      S :=
    { τ₁ := adj.counit.app S.X₁
      τ₂ := adj.counit.app S.X₂
      τ₃ := adj.counit.app S.X₃
      comm₁₂ := (adj.counit.naturality S.f).symm
      comm₂₃ := (adj.counit.naturality S.g).symm }
  rw [etaleCohomologyDirectImageEdge_apply, etaleCohomologyDirectImageEdge_apply,
    Sheaf.H.map_apply, Sheaf.H.map_apply,
    show etaleCohomologyRestrictionMap.{u, v, w} i ((etaleAbelianDirectImage.{u, v} i).obj S.X₁) r
        (x.comp hS'.extClass hqr) = _ from
      etaleCohomologyRestrictionMap_comp_extClass.{u, v, w} i hS' q r hqr x,
    Ext.comp_assoc_of_third_deg_zero, ShortComplex.ShortExact.extClass_naturality
      (hS'.map_of_exact (etaleAbelianInverseImage.{u, v} i)) hS φ,
    ← Ext.comp_assoc _ _ _ (add_zero q) (zero_add 1) (by omega)]
  rfl

/-- In degree zero the edge map is the adjunction bijection, read through the comparison of the
inverse image of the constant sheaf `ℤ` with the constant sheaf `ℤ`. -/
theorem bijective_etaleCohomologyDirectImageEdge_zero
    (B : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :
    Function.Bijective (etaleCohomologyDirectImageEdge.{u, v, w} i B 0) := by
  let adj := etaleAbelianInverseImageDirectImageAdj.{u, v} i
  let c := (etaleAbelianInverseImageConstantIso.{u, v} i).app
    (AddCommGrpCat.of (ULift.{max (u + 1) v} ℤ))
  have key : ∀ φ : (constantSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj
      (AddCommGrpCat.of (ULift ℤ)) ⟶ (etaleAbelianDirectImage.{u, v} i).obj B,
      etaleCohomologyDirectImageEdge.{u, v, w} i B 0 (Ext.mk₀ φ) =
        Ext.mk₀ (c.inv ≫ (adj.homEquiv _ _).symm φ) := by
    intro φ
    rw [etaleCohomologyDirectImageEdge_apply, etaleCohomologyRestrictionMap_apply,
      Ext.mapExactFunctor_mk₀, Sheaf.H.map_apply, Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀,
      Adjunction.homEquiv_counit, Category.assoc]
  refine ⟨fun x y hxy => ?_, fun z => ?_⟩
  · obtain ⟨φ, rfl⟩ := (Ext.mk₀_bijective _ _).2 x
    obtain ⟨ψ, rfl⟩ := (Ext.mk₀_bijective _ _).2 y
    rw [key, key] at hxy
    exact congrArg Ext.mk₀ ((adj.homEquiv _ _).symm.injective
      ((cancel_epi c.inv).1 ((Ext.mk₀_bijective _ _).1 hxy)))
  · obtain ⟨χ, rfl⟩ := (Ext.mk₀_bijective _ _).2 z
    refine ⟨Ext.mk₀ (adj.homEquiv _ _ (c.hom ≫ χ)), ?_⟩
    rw [key, Equiv.symm_apply_apply, Iso.inv_hom_id_assoc]

/-- Every class in degree `n + 1` with values in `S.X₁` is a connecting-map image when `S.X₂` is
injective. -/
private theorem exists_comp_extClass_of_injective {C : Type*} [Category C] [Abelian C]
    [HasExt.{w} C] {S : ShortComplex C} (hS : S.ShortExact) [Injective S.X₂] {X : C} {n : ℕ}
    (y : Ext X S.X₁ (n + 1)) : ∃ x : Ext X S.X₃ n, x.comp hS.extClass rfl = y :=
  Ext.covariant_sequence_exact₁ _ hS y (Ext.eq_zero_of_injective _) rfl

/-- **The inductive step.** Let `0 ⟶ B ⟶ I ⟶ Q ⟶ 0` be a short exact sequence on `Y_étale`
with `I` injective, whose direct image is short exact. If the edge map is surjective for `I` and
bijective for `Q` in degree `n`, it is bijective for `B` in degree `n + 1`. -/
theorem bijective_etaleCohomologyDirectImageEdge_succ
    {S : ShortComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})}
    (hS : S.ShortExact) (hS' : (S.map (etaleAbelianDirectImage.{u, v} i)).ShortExact)
    [Injective S.X₂] [Injective ((etaleAbelianDirectImage.{u, v} i).obj S.X₂)] (n : ℕ)
    (h₂ : Function.Surjective (etaleCohomologyDirectImageEdge.{u, v, w} i S.X₂ n))
    (h₃ : Function.Bijective (etaleCohomologyDirectImageEdge.{u, v, w} i S.X₃ n)) :
    Function.Bijective (etaleCohomologyDirectImageEdge.{u, v, w} i S.X₁ (n + 1)) := by
  have hc₂ := etaleCohomologyDirectImageEdge_comp_extClass.{u, v, w} i hS hS' n (n + 1) rfl
  have : Injective (S.map (etaleAbelianDirectImage.{u, v} i)).X₂ := ‹_›
  refine ⟨(injective_iff_map_eq_zero _).2 fun a ha => ?_, fun y => ?_⟩
  · obtain ⟨a', rfl⟩ := exists_comp_extClass_of_injective hS' a
    rw [hc₂] at ha
    obtain ⟨b, hb⟩ := Ext.covariant_sequence_exact₃ _ hS _ rfl ha
    obtain ⟨b', rfl⟩ := h₂ b
    have hb' : etaleCohomologyDirectImageEdge.{u, v, w} i S.X₃ n a' =
        etaleCohomologyDirectImageEdge.{u, v, w} i S.X₃ n
          (Sheaf.H.map ((etaleAbelianDirectImage.{u, v} i).map S.g) n b') := by
      rw [etaleCohomologyDirectImageEdge_map, Sheaf.H.map_apply, hb]
    rw [h₃.1 hb', Sheaf.H.map_apply, Ext.comp_assoc_of_second_deg_zero]
    have h0 := hS'.comp_extClass
    simp only [ShortComplex.map_g] at h0
    rw [h0, Ext.comp_zero]
  · obtain ⟨z, rfl⟩ := exists_comp_extClass_of_injective hS y
    obtain ⟨z', rfl⟩ := h₃.2 z
    exact ⟨z'.comp hS'.extClass rfl, hc₂ z'⟩

omit [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})] in
/-- The direct image of a short exact sequence `0 ⟶ S.X₁ ⟶ S.X₂ ⟶ S.X₃ ⟶ 0` is short exact when
`R¹ i_* S.X₁` vanishes. -/
private theorem shortExact_map_etaleAbelianDirectImage
    {S : ShortComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})}
    (hS : S.ShortExact)
    (h : IsZero (((etaleAbelianDirectImage.{u, v} i).rightDerived 1).obj S.X₁)) :
    (S.map (etaleAbelianDirectImage.{u, v} i)).ShortExact := by
  have hex : (S.map (etaleAbelianDirectImage.{u, v} i)).Exact :=
    hS.exact.map_of_mono_of_preservesKernel _ hS.mono_f inferInstance
  obtain ⟨δ, -, hseq⟩ :=
    Stacks.Cohomology.RightDerivedDelta.exists_delta_exact_composableArrows₅ hS
      (etaleAbelianDirectImage.{u, v} i)
  have h0 : Epi (((etaleAbelianDirectImage.{u, v} i).rightDerived 0).map S.g) :=
    ((hseq 0).exact 1).epi_f (h.eq_of_tgt _ _)
  have hepi : Epi ((etaleAbelianDirectImage.{u, v} i).map S.g) := epi_of_epi_fac
    ((etaleAbelianDirectImage.{u, v} i).rightDerivedZeroIsoSelf.hom.naturality S.g).symm
  have := hS.mono_f
  exact { exact := hex
          mono_f :=
            have := preservesMonomorphisms_of_preservesLimitsOfShape
              (etaleAbelianDirectImage.{u, v} i)
            (inferInstance : Mono ((etaleAbelianDirectImage.{u, v} i).map S.f))
          epi_g := hepi }

/-- **The edge map is bijective when the higher direct images vanish.** Let `i : Y ⟶ X` be a
morphism of schemes and `B` an abelian sheaf on `Y_étale` with `R ^ n i_* B = 0` for every
`n ≥ 1`. Then `H ^ q (X_étale, i_* B) ⟶ H ^ q (Y_étale, B)` is bijective for every `q`. -/
theorem bijective_etaleCohomologyDirectImageEdge (q : ℕ) :
    ∀ (B : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}),
      (∀ n : ℕ, 1 ≤ n →
        IsZero (((etaleAbelianDirectImage.{u, v} i).rightDerived n).obj B)) →
      Function.Bijective (etaleCohomologyDirectImageEdge.{u, v, w} i B q) := by
  have : (etaleAbelianDirectImage.{u, v} i).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (etaleAbelianInverseImageDirectImageAdj.{u, v} i)
  induction q with
  | zero => exact fun B _ => bijective_etaleCohomologyDirectImageEdge_zero.{u, v, w} i B
  | succ n hn =>
    intro B hB
    obtain ⟨S, hS, rfl, hI⟩ : ∃ S : ShortComplex (Sheaf Y.smallEtaleTopology
        AddCommGrpCat.{max (u + 1) v}), S.ShortExact ∧ S.X₁ = B ∧ Injective S.X₂ := by
      let I : InjectivePresentation B := Classical.arbitrary _
      exact ⟨ShortComplex.mk _ _ (cokernel.condition I.f),
        { exact := ShortComplex.exact_cokernel I.f }, rfl, I.injective⟩
    have hI' : ∀ m : ℕ, 1 ≤ m →
        IsZero (((etaleAbelianDirectImage.{u, v} i).rightDerived m).obj S.X₂) := fun m hm => by
      obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      exact (etaleAbelianDirectImage.{u, v} i).isZero_rightDerived_obj_injective_succ m S.X₂
    have hQ : ∀ m : ℕ, 1 ≤ m →
        IsZero (((etaleAbelianDirectImage.{u, v} i).rightDerived m).obj S.X₃) := fun m hm =>
      Stacks.Cohomology.RightDerivedDelta.isZero_rightDerived_X₃ hS _ m (hI' m hm)
        (hB (m + 1) (by omega))
    have hS' := shortExact_map_etaleAbelianDirectImage.{u, v} i hS (hB 1 le_rfl)
    exact bijective_etaleCohomologyDirectImageEdge_succ.{u, v, w} i hS hS' n
      (hn S.X₂ hI').surjective (hn S.X₃ hQ)

end Stacks.EtaleCohomology

end
