module

public import StacksFrontier.Deformation.Artin.Obstruction.SectionsAffineObjectMap
public import StacksFrontier.Deformation.Artin.Obstruction.SectionsEdgeMap
public import StacksFrontier.Deformation.Artin.Obstruction.SectionsTensorBaseChange
public import StacksFrontier.Deformation.Artin.Obstruction.SectionsThickeningSequence
public import StacksCore.Tactic.StacksAttribute

/-!
# The obstruction modules of Stacks 07YH, computed on `W`

Let `g : W → Spec Λ` be a scheme over `Λ`, let `𝓕` be a quasi-coherent `𝒪_W`-module, and for an
affine scheme `t : Spec A → Spec Λ` over `Λ` write `W_A = Spec A ×_{Spec Λ} W`, with projections
`π : W_A → Spec A` and `p : W_A → W`, and `𝓕_A = p^* 𝓕`. The obstruction modules of Stacks 07YH are
`H¹(W_A, 𝓕_A ⊗_A M)`, one space `W_A` for every base. This file compares all of them with the
cohomology of the single scheme `W`: for every `n` there is an isomorphism, natural in the
`A`-module `M`,
```
Hⁿ(W_A, 𝓕_A ⊗_A M) ≅ Hⁿ(W, 𝓕 ⊗_Λ M)
```
of abelian groups, `M` being regarded as a `Λ`-module on the right. It is the comparison of the
cohomologies of `W_A` over `A` and over `Λ` (Stacks 010U), the inverse of the edge isomorphism
`Hⁿ(W, p_* G) ≅ Hⁿ(W_A, G)` of the affine morphism `p` at the quasi-coherent module
`G = 𝓕_A ⊗_A M` (Stacks 01XC), and the identification `p_*(𝓕_A ⊗_A M) ≅ 𝓕 ⊗_Λ M`.

The comparison commutes with the connecting morphisms of short exact sequences of `A`-modules
(for `𝓕` flat over `Λ`), and with the identification of the cohomology of `W_{A'}` and `W_A` along
the thickening `W_A → W_{A'}` of a deformation situation `A' → A`. Consequently the obstruction
element of Stacks 07YH — the boundary of a section `x` of `𝓕_A` for
`0 → 𝓕_A ⊗_A I → 𝓕_{A'} → 𝓕_A → 0`, computed on `W_{A'}` and read back on `W_A` — becomes on `W`
the boundary of `x` for the sequence `0 → 𝓕 ⊗_Λ I → 𝓕 ⊗_Λ A' → 𝓕 ⊗_Λ A → 0`, obtained by
applying `𝓕 ⊗_Λ -` to `0 → I → A' → A → 0` over `Λ`. In degree zero the comparison reads a section
of `𝓕_A` as a section of `𝓕 ⊗_Λ A`, compatibly with the change of base along a morphism of objects
over affine bases.

## Main definitions

* `Deformation.Artin.SectionsSheaf.wComparison` — `Hⁿ(W_A, 𝓕_A ⊗_A M) ≅ Hⁿ(W, 𝓕 ⊗_Λ M)`, as an
  isomorphism of functors of `M`.
* `Deformation.Artin.SectionsSheaf.affineObjectSection` — the section of `𝓕_A` named by an object
  of the category fibred in groupoids attached to `T ↦ H⁰(W_T, 𝓕_T)`.
* `Deformation.Artin.SectionsSheaf.sectionsObstructionClass` — the obstruction element of
  Stacks 07YH at such an object and a deformation situation.
* `Deformation.Artin.SectionsSheaf.kernelShortComplexΛ` — `0 → I → A' → A → 0` as a sequence of
  `Λ`-modules, with `kernelShortComplexΛX₁Iso` and `kernelShortComplexΛX₃Iso` identifying its outer
  terms with `I` and `A` regarded as `Λ`-modules along `Λ → A`.

## Main results

* `Deformation.Artin.SectionsSheaf.wComparison_zero_apply` — in degree zero the comparison is
  `tensorBaseChangeSection`.
* `Deformation.Artin.SectionsSheaf.wComparison_thickening` — compatibility with the
  identification `Hⁿ(W_{A'}, i_* G) ≅ Hⁿ(W_A, G)` along a closed immersion `i : W_A → W_{A'}`.
* `Deformation.Artin.SectionsSheaf.wComparison_hom_app_comp_δ` — compatibility with connecting
  morphisms.
* `Deformation.Artin.SectionsSheaf.wComparison_sectionsObstructionClass` — **the obstruction
  element, read on `W`, is the boundary of the section for `𝓕 ⊗_Λ (0 → I → A' → A → 0)`**.
* `Deformation.Artin.SectionsSheaf.wComparison_naturality_section` — the degree-zero classes of
  two objects related by a morphism over `Spec B → Spec A` are related by `𝓕 ⊗_Λ (A → B)`.

## Implementation notes

The scheme `W_A` occurs in two spellings, `topScheme t g` (the source of `topProj t g`) and the
fibre product `pullback (Over.mk t).hom g` (the source of the projection to `W`). The two are equal
by definition, but instance search does not see through `topScheme`, so the instances needed in
the second spelling (affineness of the projection, quasi-coherence of `𝓕_A ⊗_A M`, exactness of
the direct image along the thickening) are stated in it separately. For the same reason the
additivity of `M ↦ 𝓕 ⊗_R M` is restated for a base `Spec R` with `R` a type, the spelling in which
the bases `Spec Λ` and `Spec A'` of a deformation situation occur.

The proof of `wComparison_sectionsObstructionClass` is split into several statements. Each
compares elements of cohomology groups which are equal by definition but spelled differently
(the terms of `0 → I → A' → A → 0` as `A'`-modules and as modules over `CommRingCat.of A'`, or `A`
as `A`-module and as the last term of that sequence); every such comparison is made once, in a
statement about variables, and the remaining steps are compositions of equalities whose terms
agree on the nose.

## References

* [Stacks Project, Tag 07YH](https://stacks.math.columbia.edu/tag/07YH)
* [Stacks Project, Tag 010U](https://stacks.math.columbia.edu/tag/010U)
* [Stacks Project, Tag 01XC](https://stacks.math.columbia.edu/tag/01XC)
* [Stacks Project, Tag 01F4](https://stacks.math.columbia.edu/tag/01F4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace Deformation.Artin.SectionsSheaf

/-! ### Affineness and quasi-coherence -/

section Instances

/-- The projection `W_T → W` of the base change of an affine morphism `t : T → S` is affine. -/
instance isAffineHom_pullback_snd_over {S T W : Scheme.{u}} (t : T ⟶ S) [IsAffineHom t]
    (q : W ⟶ S) : IsAffineHom (pullback.snd (Over.mk t).hom q) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback (Over.mk t).hom q) ‹_›

/-- `𝓕_T` is quasi-coherent when `𝓕` is. -/
instance isQuasicoherent_topSheaf {S W : Scheme.{u}} {A : CommRingCat.{u}} (t : Spec A ⟶ S)
    (q : W ⟶ S) (𝓕 : W.Modules) [𝓕.IsQuasicoherent] : (topSheaf t q 𝓕).IsQuasicoherent :=
  Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback _ 𝓕

/-- `𝓕 ⊗_R M = π^* M̃ ⊗ 𝓕` is quasi-coherent when `𝓕` is: the associated sheaf `M̃` is
quasi-coherent, and so are its inverse image and the tensor product of two quasi-coherent
modules. -/
instance isQuasicoherent_tensorSheafFunctor_obj {R : CommRingCat.{u}} {X : Scheme.{u}}
    (π : X ⟶ Spec R) (G : SheafOfModules.{u} X.ringCatSheaf) [G.IsQuasicoherent]
    (M : ModuleCat.{u} R) : ((tensorSheafFunctor π G).obj M).IsQuasicoherent := by
  rw [tensorSheafFunctor_obj_eq]
  exact @AlgebraicGeometry.tensorSheaf_isQuasicoherent X.toRingedSpace _ G
    (Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback π _) ‹_›

/-- `isQuasicoherent_tensorSheafFunctor_obj` at `W_T`, with the structure sheaf spelled through
the fibre product `T ×_S W`, as it is for a module on the source of the projection `W_T → W`. -/
instance isQuasicoherent_tensorSheafFunctor_obj_pullback {S W : Scheme.{u}} {A : CommRingCat.{u}}
    (t : Spec A ⟶ S) (q : W ⟶ S) (𝓕 : W.Modules) [𝓕.IsQuasicoherent] (M : ModuleCat.{u} A) :
    SheafOfModules.IsQuasicoherent (R := (pullback (Over.mk t).hom q).ringCatSheaf)
      ((tensorSheafFunctor (topProj t q) (topSheaf t q 𝓕)).obj M) :=
  isQuasicoherent_tensorSheafFunctor_obj _ _ M

/-- `additive_tensorSheafFunctor` for a base `Spec Λ` with `Λ` a type and a module spelled
`Scheme.Modules`, the spelling in which `tensorSheafFunctor g F` occurs on `W`. -/
instance additive_tensorSheafFunctor_specOf {Λ : Type u} [CommRing Λ] {X : Scheme.{u}}
    (π : X ⟶ Spec (.of Λ)) (G : X.Modules) : (tensorSheafFunctor π G).Additive :=
  additive_tensorSheafFunctor π G

/-- `additive_tensorSheafFunctor` for a base `Spec R` with `R` a type. -/
instance additive_tensorSheafFunctor_specOf' {R : Type u} [CommRing R] {X : Scheme.{u}}
    (π : X ⟶ Spec (.of R)) (G : SheafOfModules.{u} X.ringCatSheaf) :
    (tensorSheafFunctor π G).Additive :=
  additive_tensorSheafFunctor π G

end Instances

variable {Λ : Type u} [CommRing Λ] (B : BigFppfSite.{u}) (hS : B.Contains (Spec (.of Λ)))
  {W : Scheme.{u}} (g : W ⟶ Spec (.of Λ)) (F : W.Modules) [F.IsQuasicoherent]

/-! ### The comparison with the cohomology of `W` -/

/-- Elementwise form of a commutative square in a concrete category. -/
private theorem apply_comp_eq_of_comp_eq {C : Type*} [Category C] {FC : C → C → Type*}
    {CC : C → Type*} [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]
    {X Y Z T : C} {f : X ⟶ Y} {g : Y ⟶ Z} {f' : X ⟶ T} {g' : T ⟶ Z} (h : f ≫ g = f' ≫ g')
    (x : ToType X) : g (f x) = g' (f' x) :=
  (ConcreteCategory.comp_apply _ _ _).symm.trans
    ((ConcreteCategory.congr_hom h x).trans (ConcreteCategory.comp_apply _ _ _))

/-- A composite `a ≫ s ≫ e ≫ h`, contracted along `a ≫ s = b` and two commutative squares. -/
private theorem comp₃_eq_of_eq {𝒞 : Type*} [Category 𝒞] {P Q R S T U V : 𝒞} {a : P ⟶ Q} {s : Q ⟶ R}
    {b : P ⟶ R} {e : R ⟶ S} {c : P ⟶ T} {d : T ⟶ S} {h : S ⟶ U} {k : T ⟶ V} {l : V ⟶ U}
    (hB : a ≫ s = b) (hC : b ≫ e = c ≫ d) (hD : d ≫ h = k ≫ l) :
    a ≫ s ≫ e ≫ h = c ≫ k ≫ l := by
  rw [reassoc_of% hB, reassoc_of% hC, hD]

/-- Three naturality squares paste. -/
theorem comp₃_naturality {𝒞 : Type*} [Category 𝒞] {X₁ X₂ Y₁ Y₂ Z₁ Z₂ U₁ U₂ : 𝒞}
    {x : X₁ ⟶ X₂} {s₁ : X₁ ⟶ Y₁} {s₂ : X₂ ⟶ Y₂} {y : Y₁ ⟶ Y₂} {e₁ : Y₁ ⟶ Z₁} {e₂ : Y₂ ⟶ Z₂}
    {z : Z₁ ⟶ Z₂} {m₁ : Z₁ ⟶ U₁} {m₂ : Z₂ ⟶ U₂} {w : U₁ ⟶ U₂}
    (h₁ : x ≫ s₂ = s₁ ≫ y) (h₂ : y ≫ e₂ = e₁ ≫ z) (h₃ : z ≫ m₂ = m₁ ≫ w) :
    x ≫ s₂ ≫ e₂ ≫ m₂ = (s₁ ≫ e₁ ≫ m₁) ≫ w := by
  rw [reassoc_of% h₁, reassoc_of% h₂, h₃, Category.assoc, Category.assoc]

section Comparison

variable {A : CommRingCat.{u}} (t : Spec A ⟶ Spec (.of Λ))

/-- The component at `M` of `wComparison`. -/
def wComparisonApp (n : ℕ) (M : ModuleCat.{u} A) :
    ((abCohomology (topProj t g)).functor n).obj
        ((tensorSheafFunctor (topProj t g) (topSheaf t g F)).obj M) ≅
      ((abCohomology g).functor n).obj
        ((tensorSheafFunctor g F).obj ((ModuleCat.restrictScalars (Spec.preimage t).hom).obj M)) :=
  (DeltaFunctor.isoApp (spellingIso (topProj t g) (pullback.snd (Over.mk t).hom g ≫ g)) n).app
      ((tensorSheafFunctor (topProj t g) (topSheaf t g F)).obj M) ≪≫
    (edgeIso (pullback.snd (Over.mk t).hom g) g
      ((tensorSheafFunctor (topProj t g) (topSheaf t g F)).obj M) n).symm ≪≫
    ((abCohomology g).functor n).mapIso (tensorBaseChangeIso g F t M)

/-- `wComparisonApp` as the composite of its three constituents. -/
theorem wComparisonApp_hom (n : ℕ) (M : ModuleCat.{u} A) :
    (wComparisonApp g F t n M).hom =
      ((spellingIso (topProj t g) (pullback.snd (Over.mk t).hom g ≫ g)).hom.app n).app
          ((tensorSheafFunctor (topProj t g) (topSheaf t g F)).obj M) ≫
        (edgeIso (pullback.snd (Over.mk t).hom g) g
          ((tensorSheafFunctor (topProj t g) (topSheaf t g F)).obj M) n).inv ≫
        ((abCohomology g).functor n).map (tensorBaseChangeIso g F t M).hom :=
  rfl

/-- **`wComparisonApp` in degree zero is `tensorBaseChangeIso` on global sections**: the class
in `|H⁰(W_A, 𝓕_A ⊗_A M)|` of a global section is carried to the class in `|H⁰(W, 𝓕 ⊗_Λ M)|` of
its image under `p_*(𝓕_A ⊗_A M) ≅ 𝓕 ⊗_Λ M`, a global section of `p_* G` on `W` being one of `G`
on `W_A`. -/
theorem abCohomologyZeroIso_inv_app_comp_wComparisonApp_hom (M : ModuleCat.{u} A) :
    (abCohomologyZeroIso (topProj t g)).inv.app
        ((tensorSheafFunctor (topProj t g) (topSheaf t g F)).obj M) ≫
        (wComparisonApp g F t 0 M).hom =
      (pushforwardSecFIso (pullback.snd (Over.mk t).hom g)).inv.app
          ((tensorSheafFunctor (topProj t g) (topSheaf t g F)).obj M) ≫
        (secF W.ringCatSheaf ⊤).map (tensorBaseChangeIso g F t M).hom ≫
        (abCohomologyZeroIso g).inv.app _ := by
  have hB : (abCohomologyZeroIso (topProj t g)).inv.app
        ((tensorSheafFunctor (topProj t g) (topSheaf t g F)).obj M) ≫
      ((spellingIso (topProj t g) (pullback.snd (Over.mk t).hom g ≫ g)).hom.app 0).app
        ((tensorSheafFunctor (topProj t g) (topSheaf t g F)).obj M) =
      (abCohomologyZeroIso (pullback.snd (Over.mk t).hom g ≫ g)).inv.app
        ((tensorSheafFunctor (topProj t g) (topSheaf t g F)).obj M) := by
    rw [spellingIso_hom_app_zero, NatTrans.comp_app, Iso.inv_hom_id_app_assoc]
    rfl
  have hC : (abCohomologyZeroIso (pullback.snd (Over.mk t).hom g ≫ g)).inv.app
        ((tensorSheafFunctor (topProj t g) (topSheaf t g F)).obj M) ≫
      (edgeIso (pullback.snd (Over.mk t).hom g) g
        ((tensorSheafFunctor (topProj t g) (topSheaf t g F)).obj M) 0).inv =
      (pushforwardSecFIso (pullback.snd (Over.mk t).hom g)).inv.app
          ((tensorSheafFunctor (topProj t g) (topSheaf t g F)).obj M) ≫
        (abCohomologyZeroIso g).inv.app
          ((modulesPushforward (pullback.snd (Over.mk t).hom g)).obj
            ((tensorSheafFunctor (topProj t g) (topSheaf t g F)).obj M)) :=
    (Iso.comp_inv_eq _).2 ((Iso.inv_hom_id_app_assoc _ _ _).symm.trans
      (congrArg (fun k => (pushforwardSecFIso (pullback.snd (Over.mk t).hom g)).inv.app
          ((tensorSheafFunctor (topProj t g) (topSheaf t g F)).obj M) ≫ k)
        (abCohomologyZeroIso_inv_app_comp_edgeMap_app (pullback.snd (Over.mk t).hom g) g
          ((tensorSheafFunctor (topProj t g) (topSheaf t g F)).obj M)).symm))
  exact comp₃_eq_of_eq hB hC
    ((abCohomologyZeroIso g).inv.naturality (tensorBaseChangeIso g F t M).hom).symm

/-- **The obstruction modules of every base, computed on `W`.** For an affine scheme
`t : Spec A → Spec Λ` over `Λ`, the natural isomorphism
`|Hⁿ(W_A, 𝓕_A ⊗_A M)| ≅ |Hⁿ(W, 𝓕 ⊗_Λ M)|` of functors of the `A`-module `M`: the cohomology of
`W_A` over `A` is its cohomology over `Λ` (`spellingIso`), which is the cohomology of `W` of the
direct image along the affine projection `p : W_A → W` (the inverse of the edge isomorphism,
Stacks 01XC), and `p_*(𝓕_A ⊗_A M) ≅ 𝓕 ⊗_Λ M` (`tensorBaseChangeIso`). -/
def wComparison (n : ℕ) :
    tensorSheafFunctor (topProj t g) (topSheaf t g F) ⋙ (abCohomology (topProj t g)).functor n ≅
      ModuleCat.restrictScalars (Spec.preimage t).hom ⋙ tensorSheafFunctor g F ⋙
        (abCohomology g).functor n :=
  NatIso.ofComponents (wComparisonApp g F t n) fun f =>
    comp₃_naturality
      (((spellingIso (topProj t g) (pullback.snd (Over.mk t).hom g ≫ g)).hom.app n).naturality
        ((tensorSheafFunctor (topProj t g) (topSheaf t g F)).map f))
      (hom_naturality_of_inv_naturality (edgeIso (pullback.snd (Over.mk t).hom g) g _ n).symm
        (edgeIso (pullback.snd (Over.mk t).hom g) g _ n).symm _ _
        ((edgeMap (pullback.snd (Over.mk t).hom g) g n).naturality
          ((tensorSheafFunctor (topProj t g) (topSheaf t g F)).map f)))
      (((Functor.map_comp _ _ _).symm.trans
        (congrArg ((abCohomology g).functor n).map
          (tensorBaseChangeIso_hom_naturality g F t f))).trans
        (Functor.map_comp _ _ _))

/-- The components of `wComparison`. -/
theorem wComparison_hom_app (n : ℕ) (M : ModuleCat.{u} A) :
    (wComparison g F t n).hom.app M = (wComparisonApp g F t n M).hom :=
  rfl

/-- **`wComparison` in degree zero**: the class in `|H⁰(W_A, 𝓕_A ⊗_A A)|` of the section of
`𝓕_A ⊗_A A` corresponding to a section `x` of `𝓕_A` is carried to the class in
`|H⁰(W, 𝓕 ⊗_Λ A)|` of `tensorBaseChangeSection g F t x`. -/
theorem wComparison_zero_apply (x : Γ(topSheaf t g F, ⊤)) :
    (wComparison g F t 0).hom.app (ModuleCat.of A A)
        ((abCohomologyZeroIso (topProj t g)).inv.app _
          (Scheme.Modules.Hom.app
            (tensorSheafFunctorObjSelf (topProj t g) (topSheaf t g F)).inv ⊤ x)) =
      (abCohomologyZeroIso g).inv.app _ (tensorBaseChangeSection g F t x) := by
  have h := ConcreteCategory.congr_hom
    (abCohomologyZeroIso_inv_app_comp_wComparisonApp_hom g F t (ModuleCat.of A A))
    (Scheme.Modules.Hom.app (tensorSheafFunctorObjSelf (topProj t g) (topSheaf t g F)).inv ⊤ x)
  rw [wComparison_hom_app]
  exact h

end Comparison

/-! ### Compatibility of `wComparison` with the thickening identification -/

section Thickening

/-- A composite with an inverse pair in the middle, contracted. -/
private theorem comp_assoc_cancel {𝒞 : Type*} [Category 𝒞] {P Q R S U : 𝒞} {a : P ⟶ Q} {b : Q ⟶ R}
    {c : R ⟶ S} {d : S ⟶ R} {e : R ⟶ U} (h : c ≫ d = 𝟙 _) :
    (a ≫ b ≫ c) ≫ d ≫ e = a ≫ b ≫ e := by
  rw [Category.assoc, Category.assoc, reassoc_of% h]

/-- **The comparison along an exact direct image commutes with the change of affine base.** For
`i : X' ⟶ X` with exact direct image and structure morphisms `π, σ` of `X` and `π₀, σ₀` of `X'`,
`thickeningIso` over `π, π₀` followed by `spellingIso π₀ σ₀` is `spellingIso π σ` at `i_* G`
followed by `thickeningIso` over `σ, σ₀`: both are morphisms of δ-functors out of the universal
`G ↦ |Hⁿ(X, i_* G)|` which are the identity on global sections in degree zero. -/
theorem thickeningIso_hom_app_comp_spellingIso_hom_app {R R' R₀ R₀' : CommRingCat.{u}}
    {X X' : Scheme.{u}} (π : X ⟶ Spec R) (σ : X ⟶ Spec R') (i : X' ⟶ X)
    [PreservesFiniteColimits (modulesPushforward i)] (π₀ : X' ⟶ Spec R₀)
    (σ₀ : X' ⟶ Spec R₀') (n : ℕ) (G : SheafOfModules.{u} X'.ringCatSheaf) :
    ((thickeningIso π i π₀).hom.app n).app G ≫ ((spellingIso π₀ σ₀).hom.app n).app G =
      ((spellingIso π σ).hom.app n).app ((modulesPushforward i).obj G) ≫
        ((thickeningIso σ i σ₀).hom.app n).app G := by
  have key : (thickeningIso π i π₀).hom ≫ (spellingIso π₀ σ₀).hom =
      DeltaFunctor.precompHom (modulesPushforward i) (spellingIso π σ).hom ≫
        (thickeningIso σ i σ₀).hom := by
    refine DeltaFunctor.IsUniversal.hom_ext_zero _ ?_
    rw [DeltaFunctor.comp_app, DeltaFunctor.comp_app
      (DeltaFunctor.precompHom (modulesPushforward i) (spellingIso π σ).hom)
      (thickeningIso σ i σ₀).hom]
    ext G : 2
    simp only [thickeningIso_hom_app_zero, spellingIso_hom_app_zero,
      DeltaFunctor.precompHom_app, NatTrans.comp_app, thickeningZeroIso_hom_app]
    change _ = ((abCohomologyZeroIso π).hom.app ((modulesPushforward i).obj G) ≫
        (abCohomologyZeroIso σ).inv.app ((modulesPushforward i).obj G)) ≫
      (thickeningZeroIso σ i σ₀).hom.app G
    rw [thickeningZeroIso_hom_app]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
    exact comp_assoc_cancel ((abCohomologyZeroIso π₀).inv_hom_id_app G)
  exact congrArg (fun η => (η.app n).app G) key

/-- `modulesPushforwardCompIso` on components. -/
theorem modulesPushforwardCompIso_hom_app {X' X Y : Scheme.{u}}
    (i : X' ⟶ X) (p : X ⟶ Y) {p' : X' ⟶ Y} (hp : i ≫ p = p') (K : X'.Modules) :
    (modulesPushforwardCompIso i p p' hp).hom.app K =
      (eqToHom (congrArg modulesPushforward hp.symm)).app K ≫
        (Scheme.Modules.pushforwardComp i p).inv.app K :=
  rfl

/-- The comparison of `(i ≫ p)_*` with `p_* ∘ i_*` through `Scheme.Modules.pushforwardCongr` is
`modulesPushforwardCompIso`. -/
theorem pushforwardCongr_symm_trans_pushforwardComp_symm_hom_app {X' X Y : Scheme.{u}}
    (i : X' ⟶ X) (p : X ⟶ Y) {p' : X' ⟶ Y} (hp : i ≫ p = p') (K : X'.Modules) :
    ((Scheme.Modules.pushforwardCongr hp).symm ≪≫
        (Scheme.Modules.pushforwardComp i p).symm).hom.app K =
      (modulesPushforwardCompIso i p p' hp).hom.app K := by
  subst hp
  rw [modulesPushforwardCompIso_hom_app]
  refine Scheme.Modules.hom_ext _ _ fun U => ?_
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Scheme.Modules.Hom.comp_app,
    pushforwardCongr_rfl_inv_app, eqToHom_refl]
  rw [NatTrans.id_app (modulesPushforward (i ≫ p)) K]
  exact (Scheme.Modules.Hom.comp_app _ _).symm

/-- The assembly of `wComparison_thickening`, in the abstract. -/
private theorem wComparison_thickening_aux {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] (Hf : 𝒟 ⥤ 𝒞)
    {D₀ D₁ D₂ E₀ E₁ : 𝒟} {U₁ U₂ V₀ V₀' U₁' U₂' : 𝒞}
    {γ₀ : D₀ ⟶ E₀} {c : D₀ ⟶ D₂} {c' : D₂ ⟶ D₀} {β : D₁ ⟶ D₂} {β' : D₂ ⟶ D₁} {γ₁ : D₁ ⟶ E₁}
    {ρ : E₁ ⟶ E₀} {a : U₁ ⟶ U₂} {κ : U₂ ⟶ V₀} {s₀ : V₀ ⟶ V₀'} {e₀h : Hf.obj D₀ ⟶ V₀'}
    {e₀i : V₀' ⟶ Hf.obj D₀} {s₁ : U₁ ⟶ U₁'} {e₁h : Hf.obj D₁ ⟶ U₁'} {e₁i : U₁' ⟶ Hf.obj D₁}
    {s₂ : U₂ ⟶ U₂'} {κ' : U₂' ⟶ V₀'} {ε₂ : Hf.obj D₂ ⟶ U₂'} {a' : U₁' ⟶ U₂'}
    (h₁ : κ ≫ s₀ = s₂ ≫ κ') (h₂ : e₀h = Hf.map c ≫ ε₂ ≫ κ') (he₀ : e₀h ≫ e₀i = 𝟙 _)
    (hs : a ≫ s₂ = s₁ ≫ a') (he : Hf.map β ≫ ε₂ = e₁h ≫ a') (he₁ : e₁i ≫ e₁h = 𝟙 _)
    (hcc : c' ≫ c = 𝟙 _) {c₆ : D₀ ⟶ D₂} (hc₆ : c₆ = c) (h₆ : γ₀ = c₆ ≫ β' ≫ γ₁ ≫ ρ)
    (hbb : β ≫ β' = 𝟙 _) :
    a ≫ κ ≫ s₀ ≫ e₀i ≫ Hf.map γ₀ = (s₁ ≫ e₁i ≫ Hf.map γ₁) ≫ Hf.map ρ := by
  subst c₆
  have ha' : a' = e₁i ≫ Hf.map β ≫ ε₂ := by rw [he, reassoc_of% he₁]
  have h₃ : Hf.map c ≫ ε₂ ≫ κ' ≫ e₀i = 𝟙 _ := by
    rw [← he₀, h₂]
    simp only [Category.assoc]
  have hε : ε₂ ≫ κ' ≫ e₀i = Hf.map c' :=
    calc ε₂ ≫ κ' ≫ e₀i = (Hf.map c' ≫ Hf.map c) ≫ ε₂ ≫ κ' ≫ e₀i := by
          rw [← Hf.map_comp, hcc, Hf.map_id, Category.id_comp]
      _ = Hf.map c' := by rw [Category.assoc, h₃, Category.comp_id]
  have hγ : Hf.map β ≫ Hf.map c' ≫ Hf.map γ₀ = Hf.map γ₁ ≫ Hf.map ρ := by
    rw [← Hf.map_comp, ← Hf.map_comp, ← Hf.map_comp, h₆, reassoc_of% hcc, reassoc_of% hbb]
  rw [reassoc_of% h₁, reassoc_of% hs, ha']
  simp only [Category.assoc]
  rw [reassoc_of% hε, hγ]

variable {A A' : CommRingCat.{u}} (t : Spec A ⟶ Spec (.of Λ)) (t₁ : Spec A' ⟶ Spec (.of Λ))
  (α : Over.mk t ⟶ Over.mk t₁) (φ : A' ⟶ A) (hα : α.left = Spec.map φ)
  [hi : IsClosedImmersion (baseChangeMap g α)]
  [PreservesFiniteColimits (modulesPushforward (X := topScheme t₁ g) (baseChangeMap g α))]

/-- **`wComparison` is compatible with the thickening identification.** For a morphism
`α : Spec A → Spec A'` over `Spec Λ` which is `Spec φ` and whose base change
`i : W_A → W_{A'}` is a closed immersion, and an `A`-module `M`: reading
`Hⁿ(W_{A'}, 𝓕_{A'} ⊗_{A'} M)` on `W_A` through `𝓕_{A'} ⊗_{A'} M ≅ i_*(𝓕_A ⊗_A M)` and
`thickeningIso`, and then on `W` through `wComparison` of `A`, is reading it on `W` through
`wComparison` of `A'`, the two `Λ`-structures on `M` agreeing. -/
theorem wComparison_thickening (n : ℕ) (M : ModuleCat.{u} A) :
    ((abCohomology (topProj t₁ g)).functor n).map
        (pushforwardTensorSheafIsoOver t₁ t α φ g F hα hi M).hom ≫
      ((thickeningIso (topProj t₁ g) (baseChangeMap g α) (topProj t g)).hom.app n).app
        ((tensorSheafFunctor (topProj t g) (topSheaf t g F)).obj M) ≫
      (wComparison g F t n).hom.app M =
    (wComparison g F t₁ n).hom.app ((ModuleCat.restrictScalars φ.hom).obj M) ≫
      ((abCohomology g).functor n).map ((tensorSheafFunctor g F).map
        (ModuleCat.restrictScalarsComp'App (Spec.preimage t₁).hom φ.hom (Spec.preimage t).hom
          (preimage_hom_eq_comp α φ hα) M).inv) := by
  rw [wComparison_hom_app, wComparisonApp_hom, wComparison_hom_app, wComparisonApp_hom]
  exact wComparison_thickening_aux ((abCohomology g).functor n)
    (thickeningIso_hom_app_comp_spellingIso_hom_app (X := pullback (Over.mk t₁).hom g)
      (topProj t₁ g) (pullback.snd (Over.mk t₁).hom g ≫ g) (baseChangeMap g α) (topProj t g)
      (pullback.snd (Over.mk t).hom g ≫ g) n
      ((tensorSheafFunctor (topProj t g) (topSheaf t g F)).obj M))
    (edgeMap_app_pullback_snd g α g ((tensorSheafFunctor (topProj t g) (topSheaf t g F)).obj M) n)
    (edgeIso (pullback.snd (Over.mk t).hom g) g
      ((tensorSheafFunctor (topProj t g) (topSheaf t g F)).obj M) n).hom_inv_id
    (((spellingIso (topProj t₁ g) (pullback.snd (Over.mk t₁).hom g ≫ g)).hom.app n).naturality
      (pushforwardTensorSheafIsoOver t₁ t α φ g F hα hi M).hom)
    ((edgeMap (pullback.snd (Over.mk t₁).hom g) g n).naturality
      (pushforwardTensorSheafIsoOver t₁ t α φ g F hα hi M).hom)
    (edgeIso (pullback.snd (Over.mk t₁).hom g) g
      ((tensorSheafFunctor (topProj t₁ g) (topSheaf t₁ g F)).obj
        ((ModuleCat.restrictScalars φ.hom).obj M)) n).inv_hom_id
    ((modulesPushforwardCompIso (baseChangeMap g α) (pullback.snd (Over.mk t₁).hom g)
      (pullback.snd (Over.mk t).hom g) (baseChangeMap_comp_snd g α)).inv_hom_id_app
      ((tensorSheafFunctor (topProj t g) (topSheaf t g F)).obj M))
    (pushforwardCongr_symm_trans_pushforwardComp_symm_hom_app (baseChangeMap g α)
      (pullback.snd (Over.mk t₁).hom g) (baseChangeMap_comp_snd g α)
      ((tensorSheafFunctor (topProj t g) (topSheaf t g F)).obj M))
    (tensorBaseChangeIso_thickening g F t t₁ α φ hα hi M)
    ((Scheme.Modules.pushforward (pullback.snd (Over.mk t₁).hom g)).mapIso
      (pushforwardTensorSheafIsoOver t₁ t α φ g F hα hi M)).hom_inv_id

end Thickening

/-! ### Compatibility of `wComparison` with connecting morphisms -/

section Delta

/-- The assembly of `wComparison_hom_app_comp_δ`, in the abstract. -/
private theorem wComparison_δ_aux {𝒞 : Type*} [Category 𝒞] {U₃ U₃' Y₃ Z₃ U₁ U₁' Y₁ Z₁ : 𝒞}
    {s₃ : U₃ ⟶ U₃'} {e₃h : Y₃ ⟶ U₃'} {e₃i : U₃' ⟶ Y₃} {m₃ : Y₃ ⟶ Z₃} {s₁ : U₁ ⟶ U₁'}
    {e₁h : Y₁ ⟶ U₁'} {e₁i : U₁' ⟶ Y₁} {m₁ : Y₁ ⟶ Z₁} {δW : Z₃ ⟶ Z₁} {δπ : U₃ ⟶ U₁}
    {δpg : U₃' ⟶ U₁'} {δp : Y₃ ⟶ Y₁}
    (hsp : s₃ ≫ δpg = δπ ≫ s₁) (hed : e₃h ≫ δpg = δp ≫ e₁h) (hnat : m₃ ≫ δW = δp ≫ m₁)
    (he₃ : e₃i ≫ e₃h = 𝟙 _) (he₁ : e₁h ≫ e₁i = 𝟙 _) :
    (s₃ ≫ e₃i ≫ m₃) ≫ δW = δπ ≫ s₁ ≫ e₁i ≫ m₁ := by
  have h : e₃i ≫ δp = δpg ≫ e₁i :=
    calc e₃i ≫ δp = e₃i ≫ (δp ≫ e₁h) ≫ e₁i := by rw [Category.assoc, he₁, Category.comp_id]
      _ = (e₃i ≫ e₃h) ≫ δpg ≫ e₁i := by
        rw [← hed]
        simp only [Category.assoc]
      _ = δpg ≫ e₁i := by rw [he₃, Category.id_comp]
  rw [Category.assoc, Category.assoc, hnat, reassoc_of% h, reassoc_of% hsp]

variable {R : Type u} [CommRing R] (t : Spec (.of R) ⟶ Spec (.of Λ))

/-- **`p_*(𝓕_A ⊗_A K) ≅ 𝓕 ⊗_Λ K` for a short complex `K` of `A`-modules**: `tensorBaseChangeIso`
termwise. -/
def tensorBaseChangeShortComplexIso (K : ShortComplex (ModuleCat.{u} R)) :
    ShortComplex.map (C := SheafOfModules.{u} (pullback (Over.mk t).hom g).ringCatSheaf)
        ((K : ShortComplex (ModuleCat.{u} (CommRingCat.of R))).map
            (tensorSheafFunctor (topProj t g) (topSheaf t g F)) :
          ShortComplex (SheafOfModules.{u} (topScheme t g).ringCatSheaf))
        (modulesPushforward (pullback.snd (Over.mk t).hom g)) ≅
      (K.map (ModuleCat.restrictScalars (Spec.preimage t).hom)).map (tensorSheafFunctor g F) :=
  ShortComplex.isoMk (tensorBaseChangeIso g F t K.X₁) (tensorBaseChangeIso g F t K.X₂)
    (tensorBaseChangeIso g F t K.X₃) (tensorBaseChangeIso_hom_naturality g F t K.f).symm
    (tensorBaseChangeIso_hom_naturality g F t K.g).symm

/-- The direct image to `W` of `𝓕_A ⊗_A K` is short exact for a short exact sequence `K` of
`A`-modules: it is `𝓕 ⊗_Λ K`, and `𝓕` is flat over `Λ`. -/
theorem shortExact_map_modulesPushforward
    (hF : AlgebraicGeometry.IsFlatOver g.toLRSHom.toShHom F) {K : ShortComplex (ModuleCat.{u} R)}
    (hK : K.ShortExact) :
    (ShortComplex.map (C := SheafOfModules.{u} (pullback (Over.mk t).hom g).ringCatSheaf)
        ((K : ShortComplex (ModuleCat.{u} (CommRingCat.of R))).map
            (tensorSheafFunctor (topProj t g) (topSheaf t g F)) :
          ShortComplex (SheafOfModules.{u} (topScheme t g).ringCatSheaf))
        (modulesPushforward (pullback.snd (Over.mk t).hom g)) :
          ShortComplex (SheafOfModules.{u} W.ringCatSheaf)).ShortExact :=
  ShortComplex.shortExact_of_iso (tensorBaseChangeShortComplexIso g F t K).symm
    (tensorSheafFunctor_shortExact g F hF (hK.map_of_exact _))

/-- **`wComparison` commutes with the connecting morphisms.** For a short exact sequence `K` of
`A`-modules, the connecting morphism of `0 → 𝓕_A ⊗_A K₁ → 𝓕_A ⊗_A K₂ → 𝓕_A ⊗_A K₃ → 0` on
`W_A` is carried by `wComparison` to that of `0 → 𝓕 ⊗_Λ K₁ → 𝓕 ⊗_Λ K₂ → 𝓕 ⊗_Λ K₃ → 0` on `W`. -/
theorem wComparison_hom_app_comp_δ (hF : AlgebraicGeometry.IsFlatOver g.toLRSHom.toShHom F)
    {K : ShortComplex (ModuleCat.{u} R)} (hK : K.ShortExact) (n : ℕ) :
    (wComparison g F t n).hom.app K.X₃ ≫
        (abCohomology g).δ (tensorSheafFunctor_shortExact g F hF
          (hK.map_of_exact (ModuleCat.restrictScalars (Spec.preimage t).hom))) n =
      (abCohomology (topProj t g)).δ (tensorSheafFunctor_shortExact (topProj t g)
          (topSheaf t g F) (isFlatOver_topSheaf g F hF t) hK) n ≫
        (wComparison g F t (n + 1)).hom.app K.X₁ := by
  rw [wComparison_hom_app, wComparisonApp_hom, wComparison_hom_app, wComparisonApp_hom]
  exact wComparison_δ_aux
    ((spellingIso (topProj t g) (pullback.snd (Over.mk t).hom g ≫ g)).hom.comm
      (tensorSheafFunctor_shortExact (topProj t g) (topSheaf t g F)
        (isFlatOver_topSheaf g F hF t) hK) n)
    (edgeMap_δ (pullback.snd (Over.mk t).hom g) g
      (tensorSheafFunctor_shortExact (topProj t g) (topSheaf t g F)
        (isFlatOver_topSheaf g F hF t) hK)
      (shortExact_map_modulesPushforward g F t hF hK) n)
    ((abCohomology g).δ_naturality (shortExact_map_modulesPushforward g F t hF hK)
      (tensorSheafFunctor_shortExact g F hF
        (hK.map_of_exact (ModuleCat.restrictScalars (Spec.preimage t).hom)))
      (tensorBaseChangeShortComplexIso g F t K).hom n)
    (edgeIso (pullback.snd (Over.mk t).hom g) g
      ((tensorSheafFunctor (topProj t g) (topSheaf t g F)).obj K.X₃) n).inv_hom_id
    (edgeIso (pullback.snd (Over.mk t).hom g) g
      ((tensorSheafFunctor (topProj t g) (topSheaf t g F)).obj K.X₁) (n + 1)).hom_inv_id

/-- **`wComparison` carries the obstruction class to the boundary on `W`**: for a short exact
sequence `K` of `A`-modules and a class `s ∈ H⁰(W_A, 𝓕_A ⊗_A K₃)`, the obstruction class of `s`
(the boundary of `0 → 𝓕_A ⊗_A K₁ → 𝓕_A ⊗_A K₂ → 𝓕_A ⊗_A K₃ → 0` at `s`) is carried by
`wComparison` to the boundary on `W` of the image of `s`. -/
theorem wComparison_hom_app_obstructionClass
    (hF : AlgebraicGeometry.IsFlatOver g.toLRSHom.toShHom F)
    {K : ShortComplex (ModuleCat.{u} R)} (hK : K.ShortExact)
    (s : (((cohomologyDeltaFunctor (topProj t g)).functor 0).obj
      ((tensorSheafFunctor (topProj t g) (topSheaf t g F)).obj K.X₃) : Type u)) :
    (wComparison g F t 1).hom.app K.X₁
        (obstructionClass (topProj t g) (topSheaf t g F) (isFlatOver_topSheaf g F hF t) hK s) =
      (abCohomology g).δ (tensorSheafFunctor_shortExact g F hF
          (hK.map_of_exact (ModuleCat.restrictScalars (Spec.preimage t).hom))) 0
        ((wComparison g F t 0).hom.app K.X₃ s) := by
  have h := apply_comp_eq_of_comp_eq (wComparison_hom_app_comp_δ g F t hF hK 0) s
  exact h.symm

omit [F.IsQuasicoherent] in
/-- The boundary on `W` of `𝓕 ⊗_Λ K`, applied to equal classes in the spelling of the target
of `wComparison`. -/
theorem abCohomology_δ_congr (hF : AlgebraicGeometry.IsFlatOver g.toLRSHom.toShHom F)
    {K : ShortComplex (ModuleCat.{u} R)} (hK : K.ShortExact)
    {a b : ((ModuleCat.restrictScalars (Spec.preimage t).hom ⋙ tensorSheafFunctor g F ⋙
      (abCohomology g).functor 0).obj K.X₃ : Type u)} (h : a = b) :
    (abCohomology g).δ (tensorSheafFunctor_shortExact g F hF
        (hK.map_of_exact (ModuleCat.restrictScalars (Spec.preimage t).hom))) 0 a =
      (abCohomology g).δ (tensorSheafFunctor_shortExact g F hF
        (hK.map_of_exact (ModuleCat.restrictScalars (Spec.preimage t).hom))) 0 b :=
  congrArg _ h

end Delta


/-! ### The obstruction element -/

section Obstruction

/-- The global section `x ∈ H⁰(W_A, 𝓕_A)` named by an object of the category fibred in groupoids
`sectionsFibredCategory g F B hS` lying over `Spec A`. -/
abbrev affineObjectSection
    (P : AffineObject B (Spec (.of Λ)) hS (sectionsFibredCategory g F B hS)) :
    Γ(topSheaf P.alg.toScheme g F, ⊤) :=
  PresheafOfCategories.discreteFiberEquiv (sectionsPresheaf g F B hS) P.alg.over P.obj

/-- **The restriction maps of a presheaf on the big fppf site obtained from a presheaf `G` on
schemes over `S`**, between the spectra of two site algebras, are those of `G`, with the spectra
spelled as `Over.mk` of their structure morphisms. -/
theorem siteToOver_comp_forget_map_apply {S : Scheme.{u}} {hS : B.Contains S}
    (G : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{u}) {a b : SiteAlgebra B S hS} (f : b.over ⟶ a.over)
    (x : ((siteToOver B hS).op ⋙ G ⋙ forget AddCommGrpCat.{u}).obj (op a.over)) :
    ((siteToOver B hS).op ⋙ G ⋙ forget AddCommGrpCat.{u}).map f.op x =
      G.map (@Quiver.Hom.op _ _ (Over.mk b.toScheme) (Over.mk a.toScheme)
        ((siteToOver B hS).map f)) x :=
  rfl

/-- **The section named by the target of a morphism of objects over affine bases is the restriction
of the section named by its source**: `discreteFiberEquiv_eq_map_of_isHomLift`, the morphism of
the category of elements lying over `Spec B → Spec A`. -/
theorem discreteFiberEquiv_sectionsPresheaf_hom
    {P Q : AffineObject B (Spec (.of Λ)) hS (sectionsFibredCategory g F B hS)}
    (h : AffineObject.Hom P Q) :
    PresheafOfCategories.discreteFiberEquiv (sectionsPresheaf g F B hS) Q.alg.over Q.obj =
      (sectionsPresheaf g F B hS).map h.alg.specMap.op
        (PresheafOfCategories.discreteFiberEquiv (sectionsPresheaf g F B hS) P.alg.over P.obj) :=
  PresheafOfCategories.discreteFiberEquiv_eq_map_of_isHomLift (sectionsPresheaf g F B hS)
      h.alg.specMap P.obj Q.obj h.objMap h.objMap_isHomLift

/-- The base-change immersion `W_A → W_{A'}` of a deformation situation is a closed
immersion. -/
instance isClosedImmersion_baseChangeMap_thickeningOver {S : Scheme.{u}} {hS : B.Contains S}
    {a : SiteAlgebra B S hS} (t : DeformationSituation B S hS a) {W : Scheme.{u}} (q : W ⟶ S) :
    IsClosedImmersion (baseChangeMap q (thickeningOver t)) :=
  isClosedImmersion_thickening q t

/-- The direct image along the base-change immersion `W_A → W_{A'}` of a deformation situation is
exact, with the target spelled `topScheme`, as it is when the immersion is read as a morphism
into `W_{A'}`. -/
instance preservesFiniteColimits_modulesPushforward_thickeningOver {S : Scheme.{u}}
    {hS : B.Contains S} {a : SiteAlgebra B S hS} (t : DeformationSituation B S hS a)
    {W : Scheme.{u}} (q : W ⟶ S) :
    PreservesFiniteColimits
      (modulesPushforward (X := topScheme t.top.toScheme q) (baseChangeMap q (thickeningOver t))) :=
  preservesFiniteColimits_modulesPushforward (baseChangeMap q (thickeningOver t))

/-- **The obstruction element of Stacks 07YH, clause (2).** For an object `x` over `Spec A` and a
deformation situation `A' → A` with kernel `I`, the image of `x` under the boundary map
`H⁰(W_A, 𝓕_A) → H¹(W_A, 𝓕_A ⊗_A I)` of the short exact sequence
`0 → 𝓕_A ⊗_A I → 𝓕_{A'} → 𝓕_A → 0`: computed on `W_{A'}`, which has the same underlying space as
`W_A`, and read back on `W_A` through the canonical identification
`H¹(W_{A'}, i_* G) ≅ H¹(W_A, G)`. -/
def sectionsObstructionClass (hF : AlgebraicGeometry.IsFlatOver g.toLRSHom.toShHom F)
    (P : AffineObject B (Spec (.of Λ)) hS (sectionsFibredCategory g F B hS))
    (t : DeformationSituation B (Spec (.of Λ)) hS P.alg) :
    ((affineObstruction g F P).functor.obj t.kernelObj : Type u) :=
  (((thickeningIso (topProj t.top.toScheme g) (baseChangeMap g (thickeningOver t))
      (topProj P.alg.toScheme g)).hom.app 1).app _)
    (thickeningClass g F hF t (affineObjectSection B hS g F P))

end Obstruction

/-! ### The sequence `0 → I → A' → A → 0` over `Λ` -/

section Kernel

variable {B hS} {a : SiteAlgebra B (Spec (.of Λ)) hS}

/-- **`0 → I → A' → A → 0` as a sequence of `Λ`-modules**: `kernelShortComplex t` with scalars
restricted along `Λ → A'`. -/
def kernelShortComplexΛ (t : DeformationSituation B (Spec (.of Λ)) hS a) :
    ShortComplex (ModuleCat.{u} (CommRingCat.of Λ)) :=
  (kernelShortComplex t).map (ModuleCat.restrictScalars (Spec.preimage t.top.toScheme).hom)

/-- `0 → I → A' → A → 0` is short exact over `Λ`. -/
theorem kernelShortComplexΛ_shortExact (t : DeformationSituation B (Spec (.of Λ)) hS a) :
    (kernelShortComplexΛ t).ShortExact :=
  (kernelShortComplex_shortExact t).map_of_exact _

/-- The ring map `Λ → A` of the base is `Λ → A'` followed by `A' → A`. -/
theorem preimage_comp_ringMap (t : DeformationSituation B (Spec (.of Λ)) hS a) :
    Spec.preimage t.top.toScheme ≫ CommRingCat.ofHom t.hom.ringMap = Spec.preimage a.toScheme :=
  preimage_comp_eq_of_over (thickeningOver t) _ (thickeningOver_left t)

/-- The first term of `kernelShortComplexΛ` is the kernel `I` regarded as a `Λ`-module along
`Λ → A`; the identification is the identity on elements. -/
def kernelShortComplexΛX₁Iso (t : DeformationSituation B (Spec (.of Λ)) hS a) :
    (kernelShortComplexΛ t).X₁ ≅
      (ModuleCat.restrictScalars (Spec.preimage a.toScheme).hom).obj t.kernelObj :=
  (ModuleCat.restrictScalarsComp'App (Spec.preimage t.top.toScheme).hom
    (CommRingCat.ofHom t.hom.ringMap).hom (Spec.preimage a.toScheme).hom
    (preimage_hom_eq_comp (thickeningOver t) _ (thickeningOver_left t)) t.kernelObj).symm

/-- The last term of `kernelShortComplexΛ` is `A` regarded as a `Λ`-module along `Λ → A`; the
identification is the identity on elements. -/
def kernelShortComplexΛX₃Iso (t : DeformationSituation B (Spec (.of Λ)) hS a) :
    (kernelShortComplexΛ t).X₃ ≅
      (ModuleCat.restrictScalars (Spec.preimage a.toScheme).hom).obj
        (ModuleCat.of (CommRingCat.of a.carrier) (CommRingCat.of a.carrier)) :=
  (ModuleCat.restrictScalarsComp'App (Spec.preimage t.top.toScheme).hom
    (CommRingCat.ofHom t.hom.ringMap).hom (Spec.preimage a.toScheme).hom
    (preimage_hom_eq_comp (thickeningOver t) _ (thickeningOver_left t))
    (ModuleCat.of (CommRingCat.of a.carrier) (CommRingCat.of a.carrier))).symm

/-- `tensorBaseChangeIso` at the last term of `kernelShortComplex t` is its value at
`A` regarded as an `A'`-module, on the section `sectionTransportOver` of a section of `𝓕_A`. -/
theorem tensorBaseChangeIso_kernelShortComplex_X₃_app
    (t : DeformationSituation B (Spec (.of Λ)) hS a) (x : Γ(topSheaf a.toScheme g F, ⊤)) :
    Scheme.Modules.Hom.app (tensorBaseChangeIso g F t.top.toScheme (kernelShortComplex t).X₃).hom ⊤
      (sectionTransportOver t.top.toScheme a.toScheme (thickeningOver t)
        (CommRingCat.ofHom t.hom.ringMap) g F (thickeningOver_left t)
        (isClosedImmersion_thickening g t) x) =
    Scheme.Modules.Hom.app (tensorBaseChangeIso g F t.top.toScheme
      ((ModuleCat.restrictScalars (CommRingCat.ofHom t.hom.ringMap).hom).obj
        (ModuleCat.of (CommRingCat.of a.carrier) (CommRingCat.of a.carrier)))).hom ⊤
      (sectionTransportOver t.top.toScheme a.toScheme (thickeningOver t)
        (CommRingCat.ofHom t.hom.ringMap) g F (thickeningOver_left t)
        (isClosedImmersion_thickening g t) x) :=
  rfl

/-- The boundary on `W` of the sequence `kernelShortComplexΛ t`, in the two spellings of its
terms, at the class of a section of `𝓕 ⊗_Λ A` coming from a section of `𝓕_A`. -/
theorem abCohomology_δ_kernelShortComplexΛ_apply
    (hF : AlgebraicGeometry.IsFlatOver g.toLRSHom.toShHom F)
    (t : DeformationSituation B (Spec (.of Λ)) hS a) (x : Γ(topSheaf a.toScheme g F, ⊤)) :
    (abCohomology g).δ (tensorSheafFunctor_shortExact g F hF
        ((kernelShortComplex_shortExact t).map_of_exact
          (ModuleCat.restrictScalars (Spec.preimage t.top.toScheme).hom))) 0
        ((abCohomologyZeroIso g).inv.app
          ((tensorSheafFunctor g F).obj ((ModuleCat.restrictScalars
            (Spec.preimage t.top.toScheme).hom).obj (kernelShortComplex t).X₃))
          (Scheme.Modules.Hom.app (tensorBaseChangeIso g F t.top.toScheme
            ((ModuleCat.restrictScalars (CommRingCat.ofHom t.hom.ringMap).hom).obj
              (ModuleCat.of (CommRingCat.of a.carrier) (CommRingCat.of a.carrier)))).hom ⊤
            (sectionTransportOver t.top.toScheme a.toScheme (thickeningOver t)
              (CommRingCat.ofHom t.hom.ringMap) g F (thickeningOver_left t)
              (isClosedImmersion_thickening g t) x))) =
      (abCohomology g).δ (tensorSheafFunctor_shortExact g F hF
          (kernelShortComplexΛ_shortExact t)) 0
        ((abCohomologyZeroIso g).inv.app
          ((tensorSheafFunctor g F).obj ((ModuleCat.restrictScalars
            (Spec.preimage t.top.toScheme).hom).obj
            ((ModuleCat.restrictScalars (CommRingCat.ofHom t.hom.ringMap).hom).obj
              (ModuleCat.of (CommRingCat.of a.carrier) (CommRingCat.of a.carrier)))))
          (Scheme.Modules.Hom.app (tensorBaseChangeIso g F t.top.toScheme
            ((ModuleCat.restrictScalars (CommRingCat.ofHom t.hom.ringMap).hom).obj
              (ModuleCat.of (CommRingCat.of a.carrier) (CommRingCat.of a.carrier)))).hom ⊤
            (sectionTransportOver t.top.toScheme a.toScheme (thickeningOver t)
              (CommRingCat.ofHom t.hom.ringMap) g F (thickeningOver_left t)
              (isClosedImmersion_thickening g t) x))) :=
  rfl

end Kernel


/-! ### The obstruction element on `W` -/

section CruxSteps

variable {B hS} {a : SiteAlgebra B (Spec (.of Λ)) hS}

/-- The boundary of a section on `W_{A'}`, read on `W` through `wComparison` of `A'`, is the
boundary on `W` of the class of the section, read on `W` through `tensorBaseChangeIso`. -/
theorem wComparison_hom_app_obstructionClass_thickeningSection
    (hF : AlgebraicGeometry.IsFlatOver g.toLRSHom.toShHom F)
    (t : DeformationSituation B (Spec (.of Λ)) hS a) (x : Γ(topSheaf a.toScheme g F, ⊤)) :
    (wComparison g F t.top.toScheme 1).hom.app (kernelShortComplex t).X₁
        (obstructionClass (topProj t.top.toScheme g) (topSheaf t.top.toScheme g F)
          (isFlatOver_topSheaf g F hF t.top.toScheme) (kernelShortComplex_shortExact t)
          (thickeningSection g F t x)) =
      (abCohomology g).δ (tensorSheafFunctor_shortExact g F hF
          (kernelShortComplexΛ_shortExact t)) 0
        ((abCohomologyZeroIso g).inv.app
          ((tensorSheafFunctor g F).obj ((ModuleCat.restrictScalars
            (Spec.preimage t.top.toScheme).hom).obj
            ((ModuleCat.restrictScalars (CommRingCat.ofHom t.hom.ringMap).hom).obj
              (ModuleCat.of (CommRingCat.of a.carrier) (CommRingCat.of a.carrier)))))
          (Scheme.Modules.Hom.app (tensorBaseChangeIso g F t.top.toScheme
            ((ModuleCat.restrictScalars (CommRingCat.ofHom t.hom.ringMap).hom).obj
              (ModuleCat.of (CommRingCat.of a.carrier) (CommRingCat.of a.carrier)))).hom ⊤
            (sectionTransportOver t.top.toScheme a.toScheme (thickeningOver t)
              (CommRingCat.ofHom t.hom.ringMap) g F (thickeningOver_left t)
              (isClosedImmersion_thickening g t) x))) := by
  rw [wComparison_hom_app_obstructionClass g F t.top.toScheme hF
    (kernelShortComplex_shortExact t)]
  have hs : thickeningSection g F t x =
      (abCohomologyZeroIso (topProj t.top.toScheme g)).inv.app
        ((tensorSheafFunctor (topProj t.top.toScheme g) (topSheaf t.top.toScheme g F)).obj
          (kernelShortComplex t).X₃)
        (sectionTransportOver t.top.toScheme a.toScheme (thickeningOver t)
          (CommRingCat.ofHom t.hom.ringMap) g F (thickeningOver_left t)
          (isClosedImmersion_thickening g t) x) :=
    rfl
  have h₄ : (wComparison g F t.top.toScheme 0).hom.app (kernelShortComplex t).X₃
        ((abCohomologyZeroIso (topProj t.top.toScheme g)).inv.app
          ((tensorSheafFunctor (topProj t.top.toScheme g) (topSheaf t.top.toScheme g F)).obj
            (kernelShortComplex t).X₃)
          (sectionTransportOver t.top.toScheme a.toScheme (thickeningOver t)
            (CommRingCat.ofHom t.hom.ringMap) g F (thickeningOver_left t)
            (isClosedImmersion_thickening g t) x)) =
      (abCohomologyZeroIso g).inv.app
        ((tensorSheafFunctor g F).obj ((ModuleCat.restrictScalars
          (Spec.preimage t.top.toScheme).hom).obj (kernelShortComplex t).X₃))
        (Scheme.Modules.Hom.app
          (tensorBaseChangeIso g F t.top.toScheme (kernelShortComplex t).X₃).hom ⊤
          (sectionTransportOver t.top.toScheme a.toScheme (thickeningOver t)
            (CommRingCat.ofHom t.hom.ringMap) g F (thickeningOver_left t)
            (isClosedImmersion_thickening g t) x)) :=
    (ConcreteCategory.congr_hom
      (abCohomologyZeroIso_inv_app_comp_wComparisonApp_hom g F t.top.toScheme
        (kernelShortComplex t).X₃)
      (sectionTransportOver t.top.toScheme a.toScheme (thickeningOver t)
        (CommRingCat.ofHom t.hom.ringMap) g F (thickeningOver_left t)
        (isClosedImmersion_thickening g t) x) :)
  have hγ := congrArg (fun e => (abCohomologyZeroIso g).inv.app
      ((tensorSheafFunctor g F).obj ((ModuleCat.restrictScalars
        (Spec.preimage t.top.toScheme).hom).obj (kernelShortComplex t).X₃)) e)
    (tensorBaseChangeIso_kernelShortComplex_X₃_app g F t x)
  have hfin := ((congrArg (ConcreteCategory.hom ((wComparison g F t.top.toScheme 0).hom.app
      (kernelShortComplex t).X₃)) hs).trans h₄).trans hγ
  exact (abCohomology_δ_congr g F t.top.toScheme hF (kernelShortComplex_shortExact t)
    hfin).trans (abCohomology_δ_kernelShortComplexΛ_apply g F hF t x)

/-- The class on `W` of the section of `𝓕 ⊗_Λ A` named by a section of `𝓕_A`, carried to the
last term of `kernelShortComplexΛ`, is the class of the section read on `W` from `W_{A'}`. -/
theorem abCohomology_map_kernelShortComplexΛX₃Iso_inv
    (t : DeformationSituation B (Spec (.of Λ)) hS a) (x : Γ(topSheaf a.toScheme g F, ⊤)) :
    ((abCohomology g).functor 0).map
        ((tensorSheafFunctor g F).map (kernelShortComplexΛX₃Iso t).inv)
        ((abCohomologyZeroIso g).inv.app _ (tensorBaseChangeSection g F a.toScheme x)) =
      (abCohomologyZeroIso g).inv.app
          ((tensorSheafFunctor g F).obj ((ModuleCat.restrictScalars
            (Spec.preimage t.top.toScheme).hom).obj
            ((ModuleCat.restrictScalars (CommRingCat.ofHom t.hom.ringMap).hom).obj
              (ModuleCat.of (CommRingCat.of a.carrier) (CommRingCat.of a.carrier)))))
        (Scheme.Modules.Hom.app (tensorBaseChangeIso g F t.top.toScheme
          ((ModuleCat.restrictScalars (CommRingCat.ofHom t.hom.ringMap).hom).obj
            (ModuleCat.of (CommRingCat.of a.carrier) (CommRingCat.of a.carrier)))).hom ⊤
          (sectionTransportOver t.top.toScheme a.toScheme (thickeningOver t)
            (CommRingCat.ofHom t.hom.ringMap) g F (thickeningOver_left t)
            (isClosedImmersion_thickening g t) x)) := by
  have h₅ := tensorBaseChangeSection_thickening g F a.toScheme t.top.toScheme
    (thickeningOver t) (CommRingCat.ofHom t.hom.ringMap) (thickeningOver_left t)
    (isClosedImmersion_thickening g t) x
  have hX₃ : (kernelShortComplexΛX₃Iso t).inv =
      (ModuleCat.restrictScalarsComp'App (Spec.preimage t.top.toScheme).hom
        (CommRingCat.ofHom t.hom.ringMap).hom (Spec.preimage a.toScheme).hom
        (preimage_hom_eq_comp (thickeningOver t) _ (thickeningOver_left t))
        (ModuleCat.of (CommRingCat.of a.carrier) (CommRingCat.of a.carrier))).hom :=
    rfl
  have hcancel := modulesIso_hom_app_inv_app ((tensorSheafFunctor g F).mapIso
      (ModuleCat.restrictScalarsComp'App (Spec.preimage t.top.toScheme).hom
        (CommRingCat.ofHom t.hom.ringMap).hom (Spec.preimage a.toScheme).hom
        (preimage_hom_eq_comp (thickeningOver t) _ (thickeningOver_left t))
        (ModuleCat.of (CommRingCat.of a.carrier) (CommRingCat.of a.carrier)))) ⊤
    (Scheme.Modules.Hom.app (tensorBaseChangeIso g F t.top.toScheme
      ((ModuleCat.restrictScalars (CommRingCat.ofHom t.hom.ringMap).hom).obj
        (ModuleCat.of (CommRingCat.of a.carrier) (CommRingCat.of a.carrier)))).hom ⊤
      (sectionTransportOver t.top.toScheme a.toScheme (thickeningOver t)
        (CommRingCat.ofHom t.hom.ringMap) g F (thickeningOver_left t)
        (isClosedImmersion_thickening g t) x))
  rw [← apply_comp_eq_of_comp_eq ((abCohomologyZeroIso g).inv.naturality
    ((tensorSheafFunctor g F).map (kernelShortComplexΛX₃Iso t).inv))
    (tensorBaseChangeSection g F a.toScheme x), h₅, hX₃]
  exact congrArg _ hcancel

end CruxSteps

section Crux

/-- The obstruction element of `P` at `t`, read on `W` through `wComparison` of `A`, is the
boundary of the section on `W_{A'}`, read on `W` through `wComparison` of `A'`. -/
theorem wComparison_hom_app_sectionsObstructionClass_eq
    (hF : AlgebraicGeometry.IsFlatOver g.toLRSHom.toShHom F)
    (P : AffineObject B (Spec (.of Λ)) hS (sectionsFibredCategory g F B hS))
    (t : DeformationSituation B (Spec (.of Λ)) hS P.alg) :
    (wComparison g F P.alg.toScheme 1).hom.app t.kernelObj
        (sectionsObstructionClass B hS g F hF P t) =
      ((abCohomology g).functor 1).map
          ((tensorSheafFunctor g F).map (kernelShortComplexΛX₁Iso t).hom)
        ((wComparison g F t.top.toScheme 1).hom.app (kernelShortComplex t).X₁
          (obstructionClass (topProj t.top.toScheme g) (topSheaf t.top.toScheme g F)
            (isFlatOver_topSheaf g F hF t.top.toScheme) (kernelShortComplex_shortExact t)
            (thickeningSection g F t (affineObjectSection B hS g F P)))) := by
  have hPT : (eqToIso (congrArg (tensorSheafFunctor (topProj t.top.toScheme g)
        (topSheaf t.top.toScheme g F)).obj (kernelShortComplex_X₁ t)) ≪≫
      pushforwardTensorSheafIsoOver t.top.toScheme P.alg.toScheme (thickeningOver t)
        (CommRingCat.ofHom t.hom.ringMap) g F (thickeningOver_left t)
        (isClosedImmersion_thickening g t) t.kernelObj).hom =
      (pushforwardTensorSheafIsoOver t.top.toScheme P.alg.toScheme (thickeningOver t)
        (CommRingCat.ofHom t.hom.ringMap) g F (thickeningOver_left t)
        (isClosedImmersion_thickening g t) t.kernelObj).hom :=
    Category.id_comp _
  have e₁ : sectionsObstructionClass B hS g F hF P t =
      ((thickeningIso (topProj t.top.toScheme g) (baseChangeMap g (thickeningOver t))
        (topProj P.alg.toScheme g)).hom.app 1).app
          ((tensorSheafFunctor (topProj P.alg.toScheme g) (topSheaf P.alg.toScheme g F)).obj
            t.kernelObj)
        (((abCohomology (topProj t.top.toScheme g)).functor 1).map
          (eqToIso (congrArg (tensorSheafFunctor (topProj t.top.toScheme g)
              (topSheaf t.top.toScheme g F)).obj (kernelShortComplex_X₁ t)) ≪≫
            pushforwardTensorSheafIsoOver t.top.toScheme P.alg.toScheme (thickeningOver t)
              (CommRingCat.ofHom t.hom.ringMap) g F (thickeningOver_left t)
              (isClosedImmersion_thickening g t) t.kernelObj).hom
          (obstructionClass (topProj t.top.toScheme g) (topSheaf t.top.toScheme g F)
            (isFlatOver_topSheaf g F hF t.top.toScheme) (kernelShortComplex_shortExact t)
            (thickeningSection g F t (affineObjectSection B hS g F P)))) := by
    unfold sectionsObstructionClass thickeningClass
    rfl
  have h₂ : ((abCohomology (topProj t.top.toScheme g)).functor 1).map
          (eqToIso (congrArg (tensorSheafFunctor (topProj t.top.toScheme g)
              (topSheaf t.top.toScheme g F)).obj (kernelShortComplex_X₁ t)) ≪≫
            pushforwardTensorSheafIsoOver t.top.toScheme P.alg.toScheme (thickeningOver t)
              (CommRingCat.ofHom t.hom.ringMap) g F (thickeningOver_left t)
              (isClosedImmersion_thickening g t) t.kernelObj).hom ≫
        ((thickeningIso (topProj t.top.toScheme g) (baseChangeMap g (thickeningOver t))
          (topProj P.alg.toScheme g)).hom.app 1).app
          ((tensorSheafFunctor (topProj P.alg.toScheme g) (topSheaf P.alg.toScheme g F)).obj
            t.kernelObj) ≫
        (wComparison g F P.alg.toScheme 1).hom.app t.kernelObj =
      (wComparison g F t.top.toScheme 1).hom.app (kernelShortComplex t).X₁ ≫
        ((abCohomology g).functor 1).map ((tensorSheafFunctor g F).map
          (kernelShortComplexΛX₁Iso t).hom) := by
    rw [hPT]
    exact wComparison_thickening g F P.alg.toScheme t.top.toScheme (thickeningOver t)
      (CommRingCat.ofHom t.hom.ringMap) (thickeningOver_left t) 1 t.kernelObj
  have L₁ := ConcreteCategory.congr_hom h₂
    (obstructionClass (topProj t.top.toScheme g) (topSheaf t.top.toScheme g F)
      (isFlatOver_topSheaf g F hF t.top.toScheme) (kernelShortComplex_shortExact t)
      (thickeningSection g F t (affineObjectSection B hS g F P)))
  rw [e₁]
  refine Eq.trans ?_ (L₁.trans (ConcreteCategory.comp_apply _ _ _))
  exact ((ConcreteCategory.comp_apply _ _ _).trans (ConcreteCategory.comp_apply _ _ _)).symm

/-- **The obstruction element, computed on `W`.** Under `wComparison`, the obstruction element of
a deformation situation `A' → A` with kernel `I` at an object `x` over `Spec A` is the boundary of
the class of `x` — read on `W` as a section of `𝓕 ⊗_Λ A` by `tensorBaseChangeSection` — for the
short exact sequence `0 → 𝓕 ⊗_Λ I → 𝓕 ⊗_Λ A' → 𝓕 ⊗_Λ A → 0` on `W`. -/
theorem wComparison_sectionsObstructionClass
    (hF : AlgebraicGeometry.IsFlatOver g.toLRSHom.toShHom F)
    (P : AffineObject B (Spec (.of Λ)) hS (sectionsFibredCategory g F B hS))
    (t : DeformationSituation B (Spec (.of Λ)) hS P.alg) :
    (wComparison g F P.alg.toScheme 1).hom.app t.kernelObj
        (sectionsObstructionClass B hS g F hF P t) =
      ((abCohomology g).functor 1).map
          ((tensorSheafFunctor g F).map (kernelShortComplexΛX₁Iso t).hom)
        ((abCohomology g).δ
          (tensorSheafFunctor_shortExact g F hF (kernelShortComplexΛ_shortExact t)) 0
          (((abCohomology g).functor 0).map
              ((tensorSheafFunctor g F).map (kernelShortComplexΛX₃Iso t).inv)
            ((abCohomologyZeroIso g).inv.app _
              (tensorBaseChangeSection g F P.alg.toScheme (affineObjectSection B hS g F P))))) :=
  (wComparison_hom_app_sectionsObstructionClass_eq B hS g F hF P t).trans
    (congrArg (ConcreteCategory.hom (((abCohomology g).functor 1).map
      ((tensorSheafFunctor g F).map (kernelShortComplexΛX₁Iso t).hom)))
      ((wComparison_hom_app_obstructionClass_thickeningSection g F hF t
        (affineObjectSection B hS g F P)).trans
        (congrArg (ConcreteCategory.hom ((abCohomology g).δ (tensorSheafFunctor_shortExact g F hF
          (kernelShortComplexΛ_shortExact t)) 0))
          (abCohomology_map_kernelShortComplexΛX₃Iso_inv g F t
            (affineObjectSection B hS g F P)).symm)))

/-- **Change of base in degree zero, on `W`.** For a morphism `h : P → Q` of objects over affine
bases, with ring map `ψ : A → B`, the class on `W` of the section named by `Q` is the image of
the class of the section named by `P` under the map `𝓕 ⊗_Λ A → 𝓕 ⊗_Λ B` induced by `ψ`. -/
theorem wComparison_naturality_section
    {P Q : AffineObject B (Spec (.of Λ)) hS (sectionsFibredCategory g F B hS)}
    (h : AffineObject.Hom P Q) :
    (abCohomologyZeroIso g).inv.app _
        (tensorBaseChangeSection g F Q.alg.toScheme (affineObjectSection B hS g F Q)) =
      ((abCohomology g).functor 0).map ((tensorSheafFunctor g F).map
          (restrictScalarsHomOfComp (CommRingCat.ofHom h.alg.ringMap)
            (preimage_comp_eq_of_over (t := P.alg.toScheme) (t' := Q.alg.toScheme)
              ((Over.post B.inclusion).map h.alg.specMap) _ h.alg.specMap_spec)))
        ((abCohomologyZeroIso g).inv.app _
          (tensorBaseChangeSection g F P.alg.toScheme (affineObjectSection B hS g F P))) := by
  have e₁ := (discreteFiberEquiv_sectionsPresheaf_hom B hS g F h).trans
    (siteToOver_comp_forget_map_apply B (sectionsPresheafOver g F) h.alg.specMap _)
  have e₂ := (congrArg (tensorBaseChangeSection g F Q.alg.toScheme) e₁).trans
    (tensorBaseChangeSection_restriction g F P.alg.toScheme Q.alg.toScheme
      ((siteToOver B hS).map h.alg.specMap) (CommRingCat.ofHom h.alg.ringMap)
      h.alg.specMap_spec
      (PresheafOfCategories.discreteFiberEquiv (sectionsPresheaf g F B hS) P.alg.over P.obj))
  rw [show affineObjectSection B hS g F Q =
      PresheafOfCategories.discreteFiberEquiv (sectionsPresheaf g F B hS) Q.alg.over Q.obj
      from rfl,
    show affineObjectSection B hS g F P =
      PresheafOfCategories.discreteFiberEquiv (sectionsPresheaf g F B hS) P.alg.over P.obj
      from rfl, e₂]
  exact ConcreteCategory.congr_hom ((abCohomologyZeroIso g).inv.naturality
    ((tensorSheafFunctor g F).map (restrictScalarsHomOfComp (CommRingCat.ofHom h.alg.ringMap)
      (preimage_comp_eq_of_over (t := P.alg.toScheme) (t' := Q.alg.toScheme)
        ((Over.post B.inclusion).map h.alg.specMap) _ h.alg.specMap_spec))))
    (tensorBaseChangeSection g F P.alg.toScheme
      (PresheafOfCategories.discreteFiberEquiv (sectionsPresheaf g F B hS) P.alg.over P.obj))


end Crux

end Deformation.Artin.SectionsSheaf

end
