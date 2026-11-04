module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.RestrictionLongExactSequence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.IntegralPushforwardExact
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedPointDirectSumCohomology

/-!
# The edge map of a finite direct image is bijective

Let `f : X ⟶ Y` be a morphism of schemes and `G` an abelian sheaf on `X_étale`. The *edge map*
`H^q(Y, f_* G) ⟶ H^q(X, G)` is restriction along `f` followed by the counit
`f⁻¹ f_* G ⟶ G` of the inverse-image/direct-image adjunction. For `f` integral, finite for
instance, it is bijective in every degree: this is the identification
`H^q(X, G) = H^q(Y, f_* G)` of Stacks Tag 0A5D, obtained there from the vanishing of the higher
direct images (Tag 03QP) and the Leray spectral sequence (Tag 0733).

Unlike the identification `Stacks.EtaleCohomology.sheafHSmallEtalePushforwardAddEquiv`, the edge
map is built from restriction maps, so it is compatible with restriction along any other morphism
of schemes.

## Main definitions

* `Stacks.EtaleCohomology.edgeMap`: the edge map `H^q(Y, f_* G) ⟶ H^q(X, G)`.

## Main results

* `Stacks.EtaleCohomology.edgeMap_comp_mk₀`: the edge map is natural in `G`.
* `Stacks.EtaleCohomology.edgeMap_comp_extClass`: it commutes with connecting maps.
* `Stacks.EtaleCohomology.bijective_edgeMap`: it is bijective for `f` integral.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

/-- The category of abelian sheaves on the small étale site of `X` is Grothendieck abelian. -/
local instance isGrothendieckAbelian_sheaf_smallEtaleTopology' (X : Scheme.{u}) :
    IsGrothendieckAbelian.{u + 1} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) :=
  letI : EssentiallySmall.{u + 1} X.Etale := inferInstance
  Sheaf.isGrothendieckAbelian_of_essentiallySmall.{u + 1} (smallEtaleTopology X)
    AddCommGrpCat.{u + 1}

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- **The edge map** `H^q(Y, f_* G) ⟶ H^q(X, G)`: restriction along `f` followed by the counit
`f⁻¹ f_* G ⟶ G`. -/
def edgeMap (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    Sheaf.H.{u + 1} ((etaleAbelianDirectImage.{u, u + 1} f).obj G) q →+
      Sheaf.H.{u + 1} G q :=
  ((Ext.mk₀ ((etaleAbelianInverseImageDirectImageAdj.{u, u + 1} f).counit.app G)).postcomp _
      (add_zero q)).comp
    (etaleCohomologyRestrictionMap.{u, u + 1, u + 1} f
      ((etaleAbelianDirectImage.{u, u + 1} f).obj G) q)

/-- The edge map sends `x` to its restriction along `f` composed with the counit
`f⁻¹ f_* G ⟶ G`. -/
theorem edgeMap_apply (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (x : Sheaf.H.{u + 1} ((etaleAbelianDirectImage.{u, u + 1} f).obj G) q) :
    edgeMap f G q x =
      (etaleCohomologyRestrictionMap.{u, u + 1, u + 1} f
        ((etaleAbelianDirectImage.{u, u + 1} f).obj G) q x).comp
        (Ext.mk₀ ((etaleAbelianInverseImageDirectImageAdj.{u, u + 1} f).counit.app G))
        (add_zero q) :=
  rfl

/-- **The edge map is natural in the sheaf.** -/
theorem edgeMap_comp_mk₀ {G G' : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (φ : G ⟶ G')
    (q : ℕ) (x : Sheaf.H.{u + 1} ((etaleAbelianDirectImage.{u, u + 1} f).obj G) q) :
    edgeMap f G' q (x.comp (Ext.mk₀ ((etaleAbelianDirectImage.{u, u + 1} f).map φ))
        (add_zero q)) =
      (edgeMap f G q x).comp (Ext.mk₀ φ) (add_zero q) := by
  rw [edgeMap_apply, edgeMap_apply, etaleCohomologyRestrictionMap_comp_mk₀.{u, u + 1, u + 1},
    Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_third_deg_zero,
    Ext.mk₀_comp_mk₀]
  congr 2
  exact (etaleAbelianInverseImageDirectImageAdj.{u, u + 1} f).counit.naturality φ

/-- The counit, as a morphism from the inverse image of the direct image of a short complex to
the short complex. -/
@[simps]
def counitShortComplexHom (S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    (S.map (etaleAbelianDirectImage.{u, u + 1} f)).map (etaleAbelianInverseImage.{u, u + 1} f) ⟶
      S where
  τ₁ := (etaleAbelianInverseImageDirectImageAdj.{u, u + 1} f).counit.app S.X₁
  τ₂ := (etaleAbelianInverseImageDirectImageAdj.{u, u + 1} f).counit.app S.X₂
  τ₃ := (etaleAbelianInverseImageDirectImageAdj.{u, u + 1} f).counit.app S.X₃
  comm₁₂ := ((etaleAbelianInverseImageDirectImageAdj.{u, u + 1} f).counit.naturality S.f).symm
  comm₂₃ := ((etaleAbelianInverseImageDirectImageAdj.{u, u + 1} f).counit.naturality S.g).symm

/-- **The edge map commutes with connecting maps.** -/
theorem edgeMap_comp_extClass
    [PreservesFiniteColimits (etaleAbelianDirectImage.{u, u + 1} f)]
    {S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})} (hS : S.ShortExact)
    (n : ℕ) (x : Sheaf.H.{u + 1} ((etaleAbelianDirectImage.{u, u + 1} f).obj S.X₃) n) :
    edgeMap f S.X₁ (n + 1)
        (x.comp (hS.map_of_exact (etaleAbelianDirectImage.{u, u + 1} f)).extClass rfl) =
      (edgeMap f S.X₃ n x).comp hS.extClass rfl := by
  have hS' := hS.map_of_exact (etaleAbelianDirectImage.{u, u + 1} f)
  have hnat := ShortComplex.ShortExact.extClass_naturality
    (hS'.map_of_exact (etaleAbelianInverseImage.{u, u + 1} f)) hS (counitShortComplexHom f S)
  have h := etaleCohomologyRestrictionMap_comp_extClass.{u, u + 1, u + 1} f hS' n (n + 1) rfl x
  simp only [counitShortComplexHom_τ₁, counitShortComplexHom_τ₃] at hnat
  rw [edgeMap_apply, edgeMap_apply]
  refine (congrArg (fun t => t.comp (Ext.mk₀
    ((etaleAbelianInverseImageDirectImageAdj.{u, u + 1} f).counit.app S.X₁)) (add_zero _)) h).trans
    ?_
  rw [Ext.comp_assoc_of_third_deg_zero, hnat, ← Ext.comp_assoc_of_second_deg_zero]
  rfl

/-- In degree zero the edge map is the adjunction bijection. -/
theorem bijective_edgeMap_zero (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    Function.Bijective (edgeMap f G 0) := by
  set A := AddCommGrpCat.of (ULift.{u + 1} ℤ)
  set adj := etaleAbelianInverseImageDirectImageAdj.{u, u + 1} f
  set c := (etaleAbelianInverseImageConstantIso.{u, u + 1} f).app A
  have h1 : (edgeMap f G 0 : Sheaf.H.{u + 1} ((etaleAbelianDirectImage.{u, u + 1} f).obj G) 0 →
        Sheaf.H.{u + 1} G 0) =
      (fun φ => Ext.mk₀ φ) ∘ (fun ψ => c.inv ≫ ψ) ∘ (adj.homEquiv _ _).symm ∘
        Ext.homEquiv₀ := by
    funext x
    obtain ⟨φ, rfl⟩ := Ext.homEquiv₀.symm.surjective x
    simp only [Function.comp_apply, Equiv.apply_symm_apply, Ext.homEquiv₀_symm_apply]
    have : Ext.homEquiv₀ (Ext.mk₀ φ) = φ := Ext.homEquiv₀.apply_symm_apply φ
    rw [this, edgeMap_apply, etaleCohomologyRestrictionMap_apply, Ext.mapExactFunctor_mk₀,
      Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀, Adjunction.homEquiv_counit, Category.assoc]
  rw [h1]
  refine (Ext.mk₀_bijective _ _).comp (Function.Bijective.comp ?_
    ((adj.homEquiv _ _).symm.bijective.comp Ext.homEquiv₀.bijective))
  exact ⟨fun a b hab => by simpa using congrArg (fun t => c.hom ≫ t) hab,
    fun b => ⟨c.hom ≫ b, by simp⟩⟩

/-- **The edge map of an integral morphism is bijective in every degree**, for every abelian
sheaf: `H^q(Y, f_* G) = H^q(X, G)`. -/
theorem bijective_edgeMap [IsIntegralHom f] (q : ℕ) :
    ∀ G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}, Function.Bijective (edgeMap f G q) := by
  let : PreservesFiniteColimits (etaleAbelianDirectImage.{u, u + 1} f) :=
    ((exactFunctor_iff _).mp (smallEtalePushforwardAb_exact_of_isIntegralHom f)).2
  induction q with
  | zero => exact bijective_edgeMap_zero f
  | succ n ih =>
    intro G
    let S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
      ShortComplex.mk (Injective.ι G) (cokernel.π (Injective.ι G)) (cokernel.condition _)
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel _ }
    have hS' := hS.map_of_exact (etaleAbelianDirectImage.{u, u + 1} f)
    have hI : Injective S.X₂ := inferInstanceAs (Injective (Injective.under G))
    have hI' : Injective (S.map (etaleAbelianDirectImage.{u, u + 1} f)).X₂ :=
      (etaleAbelianInverseImageDirectImageAdj.{u, u + 1} f).map_injective S.X₂ hI
    constructor
    · rw [injective_iff_map_eq_zero]
      intro x hx
      obtain ⟨w, rfl⟩ := Ext.covariant_sequence_exact₁ _ hS' x (Ext.eq_zero_of_injective _) rfl
      rw [edgeMap_comp_extClass f hS n w] at hx
      obtain ⟨v, hv⟩ := Ext.covariant_sequence_exact₃ _ hS (edgeMap f S.X₃ n w) rfl hx
      obtain ⟨v', rfl⟩ := (ih S.X₂).2 v
      have hw : v'.comp (Ext.mk₀ ((etaleAbelianDirectImage.{u, u + 1} f).map S.g)) (add_zero n) =
          w := (ih S.X₃).1 (by rwa [edgeMap_comp_mk₀])
      rw [← hw, Ext.comp_assoc_of_second_deg_zero]
      have h0 : (Ext.mk₀ ((etaleAbelianDirectImage.{u, u + 1} f).map S.g)).comp hS'.extClass
          (zero_add 1) = 0 := hS'.comp_extClass
      rw [h0, Ext.comp_zero]
    · intro y
      obtain ⟨x₃, rfl⟩ := Ext.covariant_sequence_exact₁ _ hS y (Ext.eq_zero_of_injective _) rfl
      obtain ⟨w, rfl⟩ := (ih S.X₃).2 x₃
      exact ⟨w.comp hS'.extClass rfl, edgeMap_comp_extClass f hS n w⟩

end Stacks.EtaleCohomology

end
