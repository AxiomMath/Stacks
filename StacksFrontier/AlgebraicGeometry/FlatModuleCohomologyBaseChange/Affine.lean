module

public import StacksFrontier.AlgebraicGeometry.FlatModuleCohomologyBaseChange.Degreewise

/-!
# The degreewise comparison is an isomorphism over an affine open

In the situation of `StacksFrontier/AlgebraicGeometry/FlatModuleCohomologyBaseChange/Degreewise.lean`
— a cartesian square

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

with `S` and `S'` affine, `F` a quasi-coherent `𝒪_X`-module and `G` a quasi-coherent
`𝒪_{S'}`-module — the comparison

`Γ(G, ⊤) ⊗_{Γ(S, ⊤)} Γ(F, U) ⟶ Γ((f')^* G ⊗ (g')^* F, (g')⁻¹U)`

is bijective whenever `U` is an affine open of `X`. **No flatness is used**: this is affine base
change, and flatness of `G` over `S` enters only when homology is taken.

## Main results

* `Stacks.AlgebraicGeometry.ModuleBaseChange.bijective_comparisonMap_of_isAffineOpen`: **the
  comparison is bijective over an affine open.**

## Implementation notes

Write `A = Γ(S, ⊤)`, `B = Γ(S', ⊤)`, `C = Γ(X', (g')⁻¹U)`, `M = Γ(F, U)`, `N = Γ(G, ⊤)`,
`P = Γ((g')^* F, (g')⁻¹U)` and `Q = Γ((f')^* G, (g')⁻¹U)`. The proof composes seven
isomorphisms,

`N ⊗_A M ≅ N ⊗_B (B ⊗_A M) ≅ N ⊗_B P ≅ P ⊗_B N ≅ P ⊗_C (C ⊗_B N) ≅ (C ⊗_B N) ⊗_C P
  ≅ Q ⊗_C P ≅ Γ(F', (g')⁻¹U)`,

of which three are formal — two cancellations of a base change and one commutation of tensor
factors — and three are geometry proved elsewhere in the library:

* `Stacks.AlgebraicGeometry.SectionsBaseChange.bijective_sectionsBaseChangeMap_of_isAffineOpen`
  identifies `B ⊗_A M` with `P`, which is affine base change over `U` ([Stacks, Tag 02KG]);
* `AlgebraicGeometry.affinePullbackSectionsBaseChangeIso` identifies `C ⊗_B N` with `Q`, which is
  the sections of a pullback over the compatible pair of affine opens `⊤ ⊆ S'` and `(g')⁻¹U`;
* `Stacks.SectionTensorFormula.tensorSectionEquiv` identifies `Q ⊗_C P` with the sections of the
  tensor product, which is the section formula over an affine open ([Stacks, Tag 01I8]).

The commutation of factors is unavoidable with one orientation of the coefficient module: the
cancellation `M ⊗_A (A ⊗_R N) ≅ M ⊗_R N` of `TensorProduct.AlgebraTensorModule.cancelBaseChange`
cancels a base change in its *right* factor, whereas the base-changed factor here is `C ⊗_B N`,
the first one.

Composing is done on *additive* equivalences rather than on linear ones. The seven isomorphisms
are linear over three different rings, so no single ring makes the composite a linear
equivalence without restricting scalars twice; and nothing is lost, because the comparison is
already known to be `B`-linear and bijectivity is a statement about the underlying function. The
composite is then identified with the comparison by an induction over the tensor product, the
pure tensors being where every one of the seven isomorphisms is normalised.

`(g')⁻¹U` is affine because `g'` is an affine morphism, being a base change of `g`, which is
affine because `S` and `S'` are.

## References

* [Stacks Project, Tag 0GN5](https://stacks.math.columbia.edu/tag/0GN5)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 01I8](https://stacks.math.columbia.edu/tag/01I8)
-/

@[expose] public noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.SectionsBaseChange
open scoped TensorProduct

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso Stacks.SheafInternalHom.isLocalization_sheafify
  Stacks.SheafInternalHom.monoidalCategory Stacks.SheafInternalHom.sheafifyMonoidal
  Stacks.SheafInternalHom.braidedCategory Stacks.SheafInternalHom.schemeMonoidalCategory

namespace Stacks.AlgebraicGeometry.ModuleBaseChange

variable {S S' X X' : Scheme.{u}}

/-- The `Γ(S', ⊤)`-module structure on the sections of an `𝒪_{X'}`-module over `V` restricts
the `Γ(X', V)`-module structure along `f'`. -/
private theorem isScalarTower_baseModule (f' : X' ⟶ S') (M : X'.Modules) (V : X'.Opens) :
    letI := (f'.appLE ⊤ V (le_preimage_top f' _)).hom.toAlgebra
    letI := baseModule f' M V
    IsScalarTower Γ(S', ⊤) Γ(X', V) Γ(M, V) :=
  let := (f'.appLE ⊤ V (le_preimage_top f' _)).hom.toAlgebra
  let := baseModule f' M V
  Stacks.FlatSectionsDescent.isScalarTower_of_smul_eq (RingHom.id _) (fun _ _ => rfl)
    (f'.appLE ⊤ V (le_preimage_top f' _)).hom (fun _ _ => rfl) (fun _ => rfl)

/-- Over an affine open `V` of `X'`, pulling back global sections exhibits
`Γ((f')^* G, V)` as the base change of `Γ(G, ⊤)` along `Γ(S', ⊤) → Γ(X', V)`. -/
private theorem isBaseChange_coeffSection (f' : X' ⟶ S') [IsAffine S'] (G : S'.Modules)
    [G.IsQuasicoherent] {V : X'.Opens} (hV : IsAffineOpen V) :
    letI := (f'.appLE ⊤ V (le_preimage_top f' _)).hom.toAlgebra
    letI := baseModule f' ((Scheme.Modules.pullback f').obj G) V
    haveI := isScalarTower_baseModule f' ((Scheme.Modules.pullback f').obj G) V
    IsBaseChange Γ(X', V)
      ({ toFun := coeffSection f' G V
         map_add' := coeffSection_add f' G V
         map_smul' := coeffSection_smul f' G V } :
        Γ(G, ⊤) →ₗ[Γ(S', ⊤)] Γ((Scheme.Modules.pullback f').obj G, V)) :=
  let := (f'.appLE ⊤ V (le_preimage_top f' _)).hom.toAlgebra
  let := baseModule f' ((Scheme.Modules.pullback f').obj G) V
  have := isScalarTower_baseModule f' ((Scheme.Modules.pullback f').obj G) V
  AlgebraicGeometry.ModuleCat.isBaseChange_of_extendScalarsIso
    (f'.appLE ⊤ V (le_preimage_top f' _)).hom rfl
    (affinePullbackSectionsBaseChangeIso f' G (isAffineOpen_top S') hV (le_preimage_top f' _)) _
    (fun n => by rw [affinePullbackSectionsBaseChangeIso_one_tmul]; rfl)

/-- An additive map out of a tensor product that agrees with an additive equivalence on pure
tensors is bijective. -/
private theorem bijective_of_addEquiv_tmul_eq {R M N P : Type*} [CommSemiring R] [AddCommMonoid M]
    [AddCommMonoid N] [AddCommMonoid P] [Module R M] [Module R N] {φ : M ⊗[R] N →+ P}
    (Φ : M ⊗[R] N ≃+ P) (h : ∀ m n, Φ (m ⊗ₜ n) = φ (m ⊗ₜ n)) : Function.Bijective φ := by
  have key : ⇑φ = ⇑Φ := funext fun z => by
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul m n => exact (h m n).symm
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  rw [key]
  exact Φ.bijective

/-- **The degreewise comparison is bijective over an affine open.**  For a cartesian square with
affine base, a quasi-coherent `F` on `X`, a quasi-coherent `G` on `S'` and an affine open `U` of
`X`, the canonical map

`Γ(G, ⊤) ⊗_{Γ(S, ⊤)} Γ(F, U) ⟶ Γ((f')^* G ⊗ (g')^* F, (g')⁻¹U)`

is bijective.  No flatness is assumed. -/
theorem bijective_comparisonMap_of_isAffineOpen
    {g : S' ⟶ S} {f : X ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'} (H : IsPullback g' f' f g)
    [IsAffine S] [IsAffine S'] (F : X.Modules) [F.IsQuasicoherent]
    (G : S'.Modules) [G.IsQuasicoherent] {U : X.Opens} (hU : IsAffineOpen U) :
    letI := baseModule g G ⊤
    letI := baseModule f F U
    letI := baseAlgebra g
    letI := coeffTower g G
    letI := baseModule f' (tensorPullback g' f' F G) (g' ⁻¹ᵁ U)
    Function.Bijective (comparisonMap g' f' F G H U) := by
  let algAB := baseAlgebra g
  let modAN := baseModule g G ⊤
  let towerABN := coeffTower g G
  let modAM := baseModule f F U
  let modBT := baseModule f' (tensorPullback g' f' F G) (g' ⁻¹ᵁ U)
  have hg'aff : IsAffineHom g' := MorphismProperty.of_isPullback H.flip inferInstance
  have hU' : IsAffineOpen (g' ⁻¹ᵁ U) := hU.preimage g'
  let modAP := baseModule (g' ≫ f) ((Scheme.Modules.pullback g').obj F) (g' ⁻¹ᵁ U)
  let modBP := baseModule f' ((Scheme.Modules.pullback g').obj F) (g' ⁻¹ᵁ U)
  have towerAP := baseTower H ((Scheme.Modules.pullback g').obj F) (g' ⁻¹ᵁ U)
  let := (f'.appLE ⊤ (g' ⁻¹ᵁ U) (le_preimage_top f' _)).hom.toAlgebra
  let := baseModule f' ((Scheme.Modules.pullback f').obj G) (g' ⁻¹ᵁ U)
  have := isScalarTower_baseModule f' ((Scheme.Modules.pullback f').obj G) (g' ⁻¹ᵁ U)
  have := isScalarTower_baseModule f' ((Scheme.Modules.pullback g').obj F) (g' ⁻¹ᵁ U)
  let eP := LinearEquiv.ofBijective (sectionsBaseChangeMap H F U)
    (bijective_sectionsBaseChangeMap_of_isAffineOpen H F hU)
  let e1 := (TensorProduct.AlgebraTensorModule.cancelBaseChange Γ(S, ⊤) Γ(S', ⊤) Γ(S', ⊤)
    Γ(G, ⊤) Γ(F, U)).symm
  let e2 := TensorProduct.congr (LinearEquiv.refl Γ(S', ⊤) Γ(G, ⊤)) eP
  let e3 := TensorProduct.comm Γ(S', ⊤) Γ(G, ⊤)
    Γ((Scheme.Modules.pullback g').obj F, g' ⁻¹ᵁ U)
  let e4 := (TensorProduct.AlgebraTensorModule.cancelBaseChange Γ(S', ⊤) Γ(X', g' ⁻¹ᵁ U)
    Γ(X', g' ⁻¹ᵁ U) Γ((Scheme.Modules.pullback g').obj F, g' ⁻¹ᵁ U) Γ(G, ⊤)).symm
  let e5 := TensorProduct.comm Γ(X', g' ⁻¹ᵁ U)
    Γ((Scheme.Modules.pullback g').obj F, g' ⁻¹ᵁ U)
    (Γ(X', g' ⁻¹ᵁ U) ⊗[Γ(S', ⊤)] Γ(G, ⊤))
  let e6 := TensorProduct.congr (isBaseChange_coeffSection f' G hU').equiv
    (LinearEquiv.refl Γ(X', g' ⁻¹ᵁ U) Γ((Scheme.Modules.pullback g').obj F, g' ⁻¹ᵁ U))
  let e7 := Stacks.SectionTensorFormula.tensorSectionEquiv
    ((Scheme.Modules.pullback f').obj G) ((Scheme.Modules.pullback g').obj F) hU'
  let Φ : Γ(G, ⊤) ⊗[Γ(S, ⊤)] Γ(F, U) ≃+ Γ(tensorPullback g' f' F G, g' ⁻¹ᵁ U) :=
    (e1.toAddEquiv.trans (e2.toAddEquiv.trans (e3.toAddEquiv.trans (e4.toAddEquiv.trans
      (e5.toAddEquiv.trans (e6.toAddEquiv.trans e7.toAddEquiv))))))
  have hΦ : ∀ (n : Γ(G, ⊤)) (a : Γ(F, U)),
      Φ (n ⊗ₜ[Γ(S, ⊤)] a) = comparisonSection g' f' F G U n a := fun n a => by
    have h2 : e2 (n ⊗ₜ[Γ(S', ⊤)] ((1 : Γ(S', ⊤)) ⊗ₜ[Γ(S, ⊤)] a)) =
        n ⊗ₜ[Γ(S', ⊤)] pullbackUnitSections g' F U a :=
      congrArg (n ⊗ₜ[Γ(S', ⊤)] ·) ((sectionsBaseChangeMap_tmul H F U 1 a).trans (one_smul _ _))
    have h6 : e6 (((1 : Γ(X', g' ⁻¹ᵁ U)) ⊗ₜ[Γ(S', ⊤)] n) ⊗ₜ[Γ(X', g' ⁻¹ᵁ U)]
          pullbackUnitSections g' F U a) =
        coeffSection f' G (g' ⁻¹ᵁ U) n ⊗ₜ[Γ(X', g' ⁻¹ᵁ U)] pullbackUnitSections g' F U a :=
      congrArg (· ⊗ₜ[Γ(X', g' ⁻¹ᵁ U)] pullbackUnitSections g' F U a)
        (((isBaseChange_coeffSection f' G hU').equiv_tmul 1 n).trans (one_smul _ _))
    show e7 (e6 (e5 (e4 (e3 (e2 (n ⊗ₜ[Γ(S', ⊤)] ((1 : Γ(S', ⊤)) ⊗ₜ[Γ(S, ⊤)] a))))))) = _
    rw [h2]
    show e7 (e6 (((1 : Γ(X', g' ⁻¹ᵁ U)) ⊗ₜ[Γ(S', ⊤)] n) ⊗ₜ[Γ(X', g' ⁻¹ᵁ U)]
      pullbackUnitSections g' F U a)) = _
    rw [h6]
    exact Stacks.SectionTensorFormula.tensorSectionEquiv_tmul _ _ hU' _ _
  exact bijective_of_addEquiv_tmul_eq (φ := (comparisonMap g' f' F G H U).toAddMonoidHom) Φ hΦ

end Stacks.AlgebraicGeometry.ModuleBaseChange

end
