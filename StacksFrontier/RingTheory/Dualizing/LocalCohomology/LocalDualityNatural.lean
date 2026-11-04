module

public import StacksFrontier.Algebra.Homology.DerivedCategory.HomToInjectiveSingle
public import StacksFrontier.RingTheory.Dualizing.LocalCohomology.LocalDuality

/-!
# Naturality of local duality

Draft.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Dualizing

attribute [local instance] Dualizing.hasProductsOfShape_nat_derivedCategory

/-- **Maps out of local cohomology into a derived complete object.** Let `I` be a finitely
generated ideal of a commutative ring `A`, let `ε : RΓ_I(N) ⟶ N` be the counit of the adjunction
defining local cohomology, and let `X` be derived `I`-complete. Then precomposition with `ε` is a
bijection `Hom(N, X) ≃ Hom(RΓ_I(N), X)`.

Both sides are maps out of an object into a derived complete one, so they factor uniquely
through derived completion (Stacks 0G3E), and derived completion inverts `ε` (Stacks 0A6W);
naturality of the completion unit identifies precomposition with `ε` with precomposition with
its completion. -/
theorem bijective_comp_localCohomologyCounit (A : Type u) [CommRing A] (I : Ideal A)
    (hI : I.FG) (N X : DerivedCategory (ModuleCat.{u} A)) (hX : IsDerivedComplete I X) :
    Function.Bijective
      (fun g : N ⟶ X ↦ (localCohomologyAdjunction A I hI).counit.app N ≫ g) := by
  obtain ⟨r, f, hf⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hI
  change Ideal.span (Set.range f) = I at hf
  let F := DerivedCompletion.derivedCompletionFunctor A f
  let η := DerivedCompletion.derivedCompletionUnit A f
  have hε := DerivedCompletion.derivedCompletion_isReflection A f
  have hX' : IsDerivedComplete (Ideal.span (Set.range f)) X := hf ▸ hX
  let ε := (localCohomologyAdjunction A I hI).counit.app N
  have hFε : IsIso (F.map ε) := by
    have := isIso_derivedCompletion_map_cechTorsionCounit A I hI f hf N
    have key : F.map ε = F.map ((localCohomologyCechTensorIso A I hI f hf).hom.app N) ≫
        F.map ((cechTorsionCounit A f).app N) := by
      rw [← F.map_comp]
      exact congrArg F.map
        (NatTrans.congr_app (localCohomologyCechTensorIso_comp_counit A I hI f hf) N).symm
    rw [key]
    exact IsIso.comp_isIso' (Functor.map_isIso F _) this
  have hnat : ε ≫ η.app N = η.app _ ≫ F.map ε := η.naturality ε
  have hcomp : (fun g : N ⟶ X ↦ ε ≫ g) ∘ (fun φ : F.obj N ⟶ X ↦ η.app N ≫ φ) =
      (fun ψ : F.obj _ ⟶ X ↦ η.app _ ≫ ψ) ∘ (fun φ : F.obj N ⟶ X ↦ F.map ε ≫ φ) := by
    funext φ
    simp only [Function.comp_apply, ← Category.assoc, hnat]
  have hb₂ : Function.Bijective (fun φ : F.obj N ⟶ X ↦ F.map ε ≫ φ) := by
    refine ⟨fun a b hab ↦ (cancel_epi (F.map ε)).1 hab, fun ψ ↦ ⟨inv (F.map ε) ≫ ψ, ?_⟩⟩
    simp
  have hrhs := (hε.2 _ X hX').comp hb₂
  rw [← hcomp] at hrhs
  exact (Function.Bijective.of_comp_iff _ (hε.2 N X hX')).mp hrhs

/-- **Local duality against a derived complete object, natural in the source.** Let `I` be a
finitely generated ideal of a commutative ring `A`, let `X` be a derived `I`-complete object of
`D(A)` and suppose `RΓ_I(X)` is an injective module `J` placed in degree `d`, via `β`. Then for
every `K` in `D(A)`, applying `RΓ_I` and then `Hᵈ` is a bijection

`Hom_{D(A)}(K, X) ≃ Hom_A(Hᵈ_I(K), J)`.

The map is visibly natural in `K`. It is the composite of three bijections: precomposition with
the counit `RΓ_I(K) ⟶ K` (maps into a derived complete object,
`Dualizing.bijective_comp_localCohomologyCounit`), the adjunction defining `RΓ_I`, and the
identification of maps into an injective module in one degree with maps out of cohomology
(`DerivedCategory.bijective_homologyMap_comp_of_injective`).

For `A` local and complete, `I = 𝔪`, `X = ω⟦n⟧` with `ω` a normalized dualizing complex and
`J` an injective hull of the residue field, this is the local duality theorem
`Ext⁻ⁱ_A(K, ω) = Hom_A(Hⁱ_𝔪(K), E)` of Stacks 0AAK, natural in `K`. -/
theorem bijective_homology_map_localCohomology_map (A : Type u) [CommRing A] (I : Ideal A)
    (hI : I.FG) (X : DerivedCategory (ModuleCat.{u} A)) (hX : IsDerivedComplete I X)
    (J : ModuleCat.{u} A) [Injective J] (d : ℤ)
    (β : (derivedPowerTorsionProperty A I hI).ι.obj ((localCohomologyFunctor A I hI).obj X) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) d).obj J)
    (K : DerivedCategory (ModuleCat.{u} A)) :
    Function.Bijective (fun φ : K ⟶ X ↦
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) d).map
          ((derivedPowerTorsionProperty A I hI).ι.map ((localCohomologyFunctor A I hI).map φ)) ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} A) d).map β.hom ≫
          (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} A) d).hom.app J) := by
  let P := derivedPowerTorsionProperty A I hI
  let G := localCohomologyFunctor A I hI
  let adj : P.ι ⊣ G := localCohomologyAdjunction A I hI
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} A) d
  have h₁ : Function.Bijective (fun g : K ⟶ X ↦ adj.counit.app K ≫ g) :=
    bijective_comp_localCohomologyCounit A I hI K X hX
  have h₂ : Function.Bijective (fun ψ : P.ι.obj (G.obj K) ⟶ X ↦ adj.homEquiv _ _ ψ) :=
    (adj.homEquiv _ _).bijective
  have h₃ : Function.Bijective (fun χ : G.obj K ⟶ G.obj X ↦ P.ι.map χ ≫ β.hom) := by
    refine ⟨fun a b h ↦ P.ι.map_injective ((cancel_mono β.hom).1 h),
      fun y ↦ ⟨P.ι.preimage (y ≫ β.inv), ?_⟩⟩
    show P.ι.map (P.ι.preimage (y ≫ β.inv)) ≫ β.hom = y
    rw [Functor.map_preimage]
    simp
  have hcomp : (fun φ : K ⟶ X ↦ H.map (P.ι.map (G.map φ)) ≫ H.map β.hom ≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} A) d).hom.app J) =
      (fun ω' ↦ H.map ω' ≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} A) d).hom.app J) ∘
      (fun χ : G.obj K ⟶ G.obj X ↦ P.ι.map χ ≫ β.hom) ∘
      (fun ψ : P.ι.obj (G.obj K) ⟶ X ↦ adj.homEquiv _ _ ψ) ∘
      (fun g : K ⟶ X ↦ adj.counit.app K ≫ g) := by
    funext φ
    have key : adj.homEquiv _ _ (adj.counit.app K ≫ φ) = G.map φ := by
      rw [Adjunction.homEquiv_apply, G.map_comp, ← Category.assoc,
        Adjunction.right_triangle_components, Category.id_comp]
    simp only [Function.comp_apply]
    rw [key, H.map_comp, Category.assoc]
  show Function.Bijective (fun φ : K ⟶ X ↦ H.map (P.ι.map (G.map φ)) ≫ H.map β.hom ≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} A) d).hom.app J)
  rw [hcomp]
  exact (DerivedCategory.bijective_homologyMap_comp_of_injective (P.ι.obj (G.obj K)) J d).comp
    (h₃.comp (h₂.comp h₁))

end Dualizing
