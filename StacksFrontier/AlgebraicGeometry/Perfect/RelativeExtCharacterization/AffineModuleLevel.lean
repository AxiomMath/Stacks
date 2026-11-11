module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeExtCharacterization.Statement
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExtDeltaFunctorRealizationTransport
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDerivedEquivalenceBoundedBelow
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RelativeDevissage

/-!
# [Stacks, Tag 0DJV] over an affine base: uniqueness from the `Ext` `δ`-functor alone

Over `S = Spec R` the module-level uniqueness asserted by [Stacks, Tag 0DJV] holds: a
pseudo-coherent `L'` carrying isomorphisms `Ext^i(L', ℱ) ≃ Ext^i(K, E ⊗^L Lf^*ℱ)`, for `ℱ`
quasi-coherent, functorial in `ℱ` and compatible with the boundary maps, is isomorphic to the
complex `L` of [Stacks, Tag 0DJU], by an isomorphism inducing the identifications.

Composing the isomorphisms of `L'` with the inverse of those of `L` gives a `δ`-compatible family
of bijections `Ext^i(L, ℱ) → Ext^i(L', ℱ)` on quasi-coherent modules. Under the derived Spec–Γ
equivalence `D(R) ≃ D_QCoh(𝒪_{Spec R})`
(`AlgebraicGeometry.StandardModel.mapDerivedCategoryFullyFaithful`) and `Mod(R) ≃ QCoh(Spec R)`
(`AlgebraicGeometry.essImage_tilde`), with `L`, `L'` bounded above
(`AlgebraicGeometry.exists_isLE_of_isPseudoCoherentFrom`), this is the situation of
`Stacks.ExtDeltaFunctorRealization.exists_isIso_eq_comp_of_fullyFaithful_mapDerivedCategory`, which
produces the isomorphism.

The general quasi-compact quasi-separated case of the module-level uniqueness is not proved
here: the argument above uses that `Ext^n(L, -)` on modules is a quotient of a representable
functor, which fails on non-affine schemes (e.g. `L = 𝒪` on `ℙ¹`, `n = 1`), and realizing maps
are unique only up to module-level ghosts, so local realizations do not glue directly.

## Main results

* `exists_unique_relativeExt_representative_spec`: **[Stacks, Tag 0DJV]** for `S = Spec R`, with
  the module-level uniqueness.

## References

* [Stacks Project, Tag 0DJV](https://stacks.math.columbia.edu/tag/0DJV)
* [Stacks Project, Tag 0DJU](https://stacks.math.columbia.edu/tag/0DJU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open Opposite MonoidalCategory AlgebraicGeometry

universe u

attribute [local implicit_reducible] TopCat.Sheaf structureSheafRing CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

namespace Stacks.AlgebraicGeometry.RelativeExtCharacterization

open Stacks.SheafOfModules Stacks.AlgebraicGeometry.RelativeDerivedHomDual
open Stacks.Cohomology.RelativeExtCanonical

attribute [local instance] derivedMonoidalStructure derivedSymmetricStructure

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R)

/-- **[Stacks, Tag 0DJV], for `S = Spec R` affine, with the module-level uniqueness.** Let
`f : X ⟶ Spec R` be proper, flat and of finite presentation, `E ∈ D(𝒪_X)` perfect relative to
`Spec R` and `K ∈ D(𝒪_X)` pseudo-coherent. The pseudo-coherent complex `L` on `Spec R` of
[Stacks, Tag 0DJU], with `Rf_*R𝓗om(K, E) ≅ R𝓗om(L, 𝒪)`, carries isomorphisms
`Ext^i(L, ℱ) ≃ Ext^i(K, E ⊗^L Lf^*ℱ)` for quasi-coherent `ℱ`, functorial in `ℱ` and compatible
with the boundary maps, induced by a natural identification `θ` on `D^+_{QCoh}` that
characterizes `L` (all as in
`Stacks.AlgebraicGeometry.RelativeExtCharacterization.exists_unique_relativeExt_representative`).
Moreover `L` is characterized by the `Ext` isomorphisms alone, which is the module-level
uniqueness of the remark: any pseudo-coherent `L'` with
isomorphisms `ε'_{ℱ,i} : Ext^i(L', ℱ) ≃ Ext^i(K, E ⊗^L Lf^*ℱ)` for quasi-coherent `ℱ`,
functorial in `ℱ` and compatible with the boundary maps, is isomorphic to `L` by an isomorphism
`g : L' ≅ L` with `ε'(g ∘ x) = ε(x)`. -/
theorem exists_unique_relativeExt_representative_spec [IsProper f] [Flat f]
    [LocallyOfFinitePresentation f] (E K : DStd X) (hE : IsRelPerfect f E)
    (hK : IsPseudoCoherentStd K) :
    ∃ L : DStd (Spec R), IsPseudoCoherentStd L ∧
      Nonempty ((pushStd f).obj (rhom K E) ≅ rhom L (unitObj (Spec R))) ∧
      ∃ θ : ShiftedHom.NaturalHomIdentification (𝟭 (DStd (Spec R))) (tensorPull f E) L K
          (boundedBelowQCoh (Spec R)),
        (∀ {F F' : (Spec R).Modules} (hF : F.IsQuasicoherent) (hF' : F'.IsQuasicoherent)
            (g : F ⟶ F') (i : ℤ)
            (x : ShiftedHom L ((RelativeDerivedHomDual.singleStd (Spec R) 0).obj F) i),
          extEquiv θ F' hF' i (x ≫ ((RelativeDerivedHomDual.singleStd (Spec R) 0).map g)⟦i⟧') =
            extEquiv θ F hF i x ≫
              ((tensorPull f E).map ((RelativeDerivedHomDual.singleStd (Spec R) 0).map g))⟦i⟧') ∧
        (∀ {T : ShortComplex (Spec R).Modules} (hT : T.ShortExact) (h₁ : T.X₁.IsQuasicoherent)
            (h₃ : T.X₃.IsQuasicoherent) (i j : ℤ) (hij : 1 + i = j)
            (x : ShiftedHom L ((RelativeDerivedHomDual.singleStd (Spec R) 0).obj T.X₃) i),
          extEquiv θ T.X₁ h₁ j (ShiftedHom.comp x (singleδStd hT) hij) =
            (extEquiv θ T.X₃ h₃ i x).comp (ShiftedHom.map (singleδStd hT) (tensorPull f E))
              hij) ∧
        (∀ (L' : DStd (Spec R)), IsPseudoCoherentStd L' →
          ∀ θ' : ShiftedHom.NaturalHomIdentification (𝟭 (DStd (Spec R))) (tensorPull f E) L' K
            (boundedBelowQCoh (Spec R)),
          ∃ φ : L' ≅ L, ∀ (N : DStd (Spec R)) (hN : boundedBelowQCoh (Spec R) N) (x : L ⟶ N),
            θ'.equiv N hN (φ.hom ≫ x) = θ.equiv N hN x) ∧
        ∀ (L' : DStd (Spec R)), IsPseudoCoherentStd L' →
          ∀ ε' : ∀ (F : (Spec R).Modules), F.IsQuasicoherent → ∀ i : ℤ,
              ShiftedHom L' ((RelativeDerivedHomDual.singleStd (Spec R) 0).obj F) i ≃+
                ShiftedHom K
                  ((tensorPull f E).obj ((RelativeDerivedHomDual.singleStd (Spec R) 0).obj F)) i,
          (∀ {F F' : (Spec R).Modules} (hF : F.IsQuasicoherent) (hF' : F'.IsQuasicoherent)
              (g : F ⟶ F') (i : ℤ)
              (x : ShiftedHom L' ((RelativeDerivedHomDual.singleStd (Spec R) 0).obj F) i),
            ε' F' hF' i (x ≫ ((RelativeDerivedHomDual.singleStd (Spec R) 0).map g)⟦i⟧') =
              ε' F hF i x ≫
                ((tensorPull f E).map ((RelativeDerivedHomDual.singleStd (Spec R) 0).map g))⟦i⟧') →
          (∀ {T : ShortComplex (Spec R).Modules} (hT : T.ShortExact) (h₁ : T.X₁.IsQuasicoherent)
              (h₃ : T.X₃.IsQuasicoherent) (i j : ℤ) (hij : 1 + i = j)
              (x : ShiftedHom L' ((RelativeDerivedHomDual.singleStd (Spec R) 0).obj T.X₃) i),
            ε' T.X₁ h₁ j (ShiftedHom.comp x (singleδStd hT) hij) =
              (ε' T.X₃ h₃ i x).comp (ShiftedHom.map (singleδStd hT) (tensorPull f E)) hij) →
          ∃ g : L' ≅ L, ∀ (F : (Spec R).Modules) (hF : F.IsQuasicoherent) (i : ℤ)
            (x : ShiftedHom L ((RelativeDerivedHomDual.singleStd (Spec R) 0).obj F) i),
            ε' F hF i (g.hom ≫ x) = extEquiv θ F hF i x := by
  obtain ⟨L, hL, hiso, θ, h₁, h₂, h₃⟩ := exists_unique_relativeExt_representative f E K hE hK
  refine ⟨L, hL, hiso, θ, h₁, h₂, h₃, fun L' hL' ε' hε'₁ hε'₂ ↦ ?_⟩
  let : HasDerivedCategory (ModuleCat.{u} R) := HasDerivedCategory.standard _
  let : HasDerivedCategory (Spec R).Modules := HasDerivedCategory.standard _
  let : HasDerivedCategory (StructureSheafModules (Spec R).sheaf) := HasDerivedCategory.standard _
  -- a pseudo-coherent complex on `Spec R` is `M̃` for a bounded above `M ∈ D(R)`
  have hmodel : ∀ A : DStd (Spec R), IsPseudoCoherentStd A →
      ∃ (A₀ : DerivedCategory (ModuleCat.{u} R)) (b : ℤ), A₀.IsLE b ∧
        Nonempty (A ≅ (tilde.functor R).mapDerivedCategory.obj A₀) := by
    intro A hA
    obtain ⟨A₀, ⟨e⟩⟩ := AlgebraicGeometry.StandardModel.exists_iso_mapDerivedCategory R A
      (fun q ↦ @Stacks.PseudoCoherentHocolim.isQuasicoherent_homology_of_isPseudoCoherent _
        (HasDerivedCategory.standard _) A hA q)
    obtain ⟨K₀, hK₀, hK₀e⟩ := hA
    obtain ⟨b, hb⟩ := AlgebraicGeometry.exists_isLE_of_isPseudoCoherentFrom A 0
      ⟨K₀, hK₀ 0, hK₀e⟩
    refine ⟨A₀, b, ?_, ⟨e.symm⟩⟩
    refine (DerivedCategory.isLE_iff _ _).2 fun i hi ↦ ?_
    rw [← AlgebraicGeometry.StandardModel.isZero_homology_mapDerivedCategory_obj_iff]
    exact ((DerivedCategory.isLE_iff A b).1 hb i hi).of_iso
      ((DerivedCategory.homologyFunctor (Spec R).Modules i).mapIso e)
  obtain ⟨L₀, a, ha, ⟨e⟩⟩ := hmodel L hL
  obtain ⟨L₀', a', ha', ⟨e'⟩⟩ := hmodel L' hL'
  -- the `δ`-compatible family of bijections `Ext^n(L, ℱ) → Ext^n(L', ℱ)`
  let φ : ∀ (n : ℤ) (G : (Spec R).Modules), G.IsQuasicoherent →
      (L ⟶ ((DerivedCategory.singleFunctor (Spec R).Modules 0).obj G)⟦n⟧) →
        (L' ⟶ ((DerivedCategory.singleFunctor (Spec R).Modules 0).obj G)⟦n⟧) :=
    fun n G hG x ↦ (ε' G hG n).symm (extEquiv θ G hG n x)
  have hφ : ∀ n G hG x, ε' G hG n (φ n G hG x) = extEquiv θ G hG n x :=
    fun _ _ _ _ ↦ AddEquiv.apply_symm_apply _ _
  obtain ⟨g, hg, hgφ⟩ :=
    Stacks.ExtDeltaFunctorRealization.exists_isIso_eq_comp_of_fullyFaithful_mapDerivedCategory
      (tilde.functor R) (AlgebraicGeometry.StandardModel.mapDerivedCategoryFullyFaithful R)
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)
      (fun M ↦ (inferInstance : ((tilde.functor R).obj M).IsQuasicoherent))
      (fun G hG ↦ by rwa [← AlgebraicGeometry.essImage_tilde] at hG)
      a a' e e' φ
      (fun n G G' hG hG' u x ↦ (ε' G' hG' n).injective
        ((hφ n G' hG' _).trans ((h₁ hG hG' u n x).trans
          ((congrArg (· ≫ _) (hφ n G hG x).symm).trans (hε'₁ hG hG' u n (φ n G hG x)).symm))))
      (fun {T} hT hT₁ hT₃ n m hnm x ↦ (ε' T.X₁ hT₁ m).injective
        ((hφ m T.X₁ hT₁ _).trans ((h₂ hT hT₁ hT₃ n m hnm x).trans
          ((congrArg (fun y ↦ ShiftedHom.comp y
              (ShiftedHom.map (singleδStd hT) (tensorPull f E)) hnm)
            (hφ n T.X₃ hT₃ x).symm).trans
            (hε'₂ hT hT₁ hT₃ n m hnm (φ n T.X₃ hT₃ x)).symm))))
      (fun n G hG ↦ (ε' G hG n).symm.bijective.comp (extEquiv θ G hG n).bijective)
  exact ⟨@asIso _ _ _ _ g hg, fun G hG i x ↦
    (congrArg (ε' G hG i) (hgφ i G hG x).symm).trans (hφ i G hG x)⟩

end Stacks.AlgebraicGeometry.RelativeExtCharacterization
