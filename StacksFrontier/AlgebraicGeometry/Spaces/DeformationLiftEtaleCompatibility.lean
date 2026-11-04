module

public import StacksFrontier.AlgebraicGeometry.Spaces.DeformationLiftActionNaturality
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsMapEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.DerivationMovePostcomposition

/-!
# Compatibility of the action with étale localization

[Stacks Project, Tag 0CK8].  Consider a commutative diagram of first order thickenings of
algebraic spaces over `S`
```
(T₂ ⊂ T₂') --(a₂, a₂')--> (X₂ ⊂ X₂')        X₂' --> B₂
   |                          |               |       |
 (h, h')                   (f, f')            v       v
   v                          v              X₁' --> B₁
(T₁ ⊂ T₁') --(a₁, a₁')--> (X₁ ⊂ X₁')
```
with `X₂ → X₁` and `B₂ → B₁` étale.  For an `𝒪_{T₁}`-linear `θ₁ : a₁^*Ω_{X₁/B₁} ⟶ 𝒞_{T₁/T₁'}` let
`θ₂` be the composition
`a₂^*Ω_{X₂/B₂} = h^*a₁^*Ω_{X₁/B₁} ⟶ h^*𝒞_{T₁/T₁'} ⟶ 𝒞_{T₂/T₂'}`.  Then
`(θ₂ · a₂') ≫ f' = h' ≫ (θ₁ · a₁')`, the actions being those of [Stacks Project, Tag 0CK6]
(`AlgebraicGeometry.Space.derivationMove_comp_of_etale`).

The equality sign is the identification `f^*Ω_{X₁/B₁} = Ω_{X₂/B₂}` of [Stacks Project, Tag 04CU]:
the canonical map `c_f` of [Stacks Project, Tag 04CX] is an isomorphism when `f` and `B₂ ⟶ B₁` are
étale (`AlgebraicGeometry.Space.isIso_sheafOfDifferentialsMap_of_isEtale`), and `θ₂` is
`a₂^*(c_f)^{-1}` followed by `a₂^*f^* = (a₂ ≫ f)^* = (h ≫ a₁)^* = h^*a₁^*`, by `h^*θ₁` and by the
conormal map of `(h, h')` (`AlgebraicGeometry.Space.etaleLocalizedDerivationDatum`).

## References

* [Stacks Project, Tag 0CK8](https://stacks.math.columbia.edu/tag/0CK8)
* [Stacks Project, Tag 0CK6](https://stacks.math.columbia.edu/tag/0CK6)
* [Stacks Project, Tag 04CU](https://stacks.math.columbia.edu/tag/04CU)
* [Stacks Project, Tag 04CX](https://stacks.math.columbia.edu/tag/04CX)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Congr

variable {X W T : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)
  (W₀ : ClosedSubspaces B S hS W.1)
  (e₀ : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
    (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS))
  (q : W ⟶ T) (hZ : IsFirstOrderThickening B S hS X Z.1)

/-- The action `θ · c` depends only on `c` and `θ`. -/
theorem derivationMove_congr {c c' : X ⟶ W} (hcc : c = c')
    (hc : subspaceInclusion B S hS X Z ≫ c = e₀ ≫ subspaceInclusion B S hS W W₀)
    (hc' : subspaceInclusion B S hS X Z ≫ c' = e₀ ≫ subspaceInclusion B S hS W W₀)
    {θ θ' : (modulePullback B S hS e₀).obj
        (sheafOfDifferentials B S hS (subspaceInclusion B S hS W W₀ ≫ q)) ⟶
      conormalModule B S hS X Z} (hθ : θ = θ') (p : X ⟶ T) (hcq : c ≫ q = p)
    (hcq' : c' ≫ q = p) :
    derivationMove B S hS Z W₀ e₀ q hZ c hc θ p hcq =
      derivationMove B S hS Z W₀ e₀ q hZ c' hc' θ' p hcq' := by
  subst hcc hθ
  rfl

end Congr

section EtaleDatum

variable {Q R R'' T T'' P : AlgebraicSpaces B S hS} (b : R ⟶ T) (b'' : R'' ⟶ T'') (f₀ : R ⟶ R'')
  (t : T ⟶ T'')
  (hcomm : @CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ f₀ b'' =
    @CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ b t) (e : Q ⟶ R) (g : Q ⟶ P)
  (a : P ⟶ R'')
  (hga : @CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ g a =
    @CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ e f₀)
  (hiso : IsIso (sheafOfDifferentialsMap B S hS f₀ b'' b t hcomm))
  (C₁ : Modules.{u, u} B S hS P.1 P.2) (C : Modules.{u, u} B S hS Q.1 Q.2)
  (θ₁ : (modulePullback B S hS a).obj (sheafOfDifferentials B S hS b'') ⟶ C₁)
  (κ : (modulePullback B S hS g).obj C₁ ⟶ C)

/-- **The datum `θ₂` of [Stacks Project, Tag 0CK8].**  For `θ₁ : a^*Ω_{R''/T''} ⟶ C₁` and
`κ : g^*C₁ ⟶ C`, `θ₂` is the composition
`e^*Ω_{R/T} = e^*f₀^*Ω_{R''/T''} = (e ≫ f₀)^*Ω_{R''/T''} = g^*a^*Ω_{R''/T''} ⟶ g^*C₁ ⟶ C`:
the first identification the inverse of the inverse image along `e` of the canonical map
`c_{f₀} : f₀^*Ω_{R''/T''} ⟶ Ω_{R/T}` of [Stacks Project, Tag 04CX] when it is an isomorphism (by
[Stacks Project, Tag 04CU] when `f₀` and `t` are étale), the next two the comparisons of
[Stacks Project, Tag 03LU] along `e ≫ f₀ = g ≫ a`, then the inverse image of `θ₁` and `κ`.  In
Tag 0CK8, `(g, a, e, f₀) = (h, a₁, a₂, f)` and `κ` is the conormal map of `(h, h')` of
[Stacks Project, Tag 04CP]. -/
noncomputable def etaleLocalizedDerivationDatum :
    (modulePullback B S hS e).obj (sheafOfDifferentials B S hS b) ⟶ C :=
  postcompInverseDatum B S hS b b'' f₀ t hcomm e C (hiso := hiso)
    ((modulePullbackTriangle B S hS hga).hom.app (sheafOfDifferentials B S hS b'') ≫
      (modulePullback B S hS g).map θ₁ ≫ κ)

/-- The datum of the postcomposition law attached to `θ₂` is `g^*θ₁` followed by `κ`. -/
theorem postcompDerivationDatum_etaleLocalizedDerivationDatum :
    postcompDerivationDatum B S hS b b'' f₀ t hcomm e C
        (etaleLocalizedDerivationDatum B S hS b b'' f₀ t hcomm e g a hga hiso C₁ C θ₁ κ) =
      (modulePullbackTriangle B S hS hga).hom.app (sheafOfDifferentials B S hS b'') ≫
        (modulePullback B S hS g).map θ₁ ≫ κ :=
  postcompDerivationDatum_postcompInverseDatum B S hS b b'' f₀ t hcomm e C (hiso := hiso) _

end EtaleDatum

section EtaleLocalization

variable {T₁' T₂' X₁' X₂' B₁ B₂ : AlgebraicSpaces B S hS}
  (Z₁ : ClosedSubspaces B S hS T₁'.1) (Z₂ : ClosedSubspaces B S hS T₂'.1)
  (W₁ : ClosedSubspaces B S hS X₁'.1) (W₂ : ClosedSubspaces B S hS X₂'.1)
  (h' : T₂' ⟶ T₁')
  (h : (⟨Z₂.1.toFunctor, Z₂.2.1⟩ : AlgebraicSpaces B S hS) ⟶
    (⟨Z₁.1.toFunctor, Z₁.2.1⟩ : AlgebraicSpaces B S hS))
  (hh : subspaceInclusion B S hS T₂' Z₂ ≫ h' = h ≫ subspaceInclusion B S hS T₁' Z₁)
  (a₁' : T₁' ⟶ X₁')
  (a₁ : (⟨Z₁.1.toFunctor, Z₁.2.1⟩ : AlgebraicSpaces B S hS) ⟶
    (⟨W₁.1.toFunctor, W₁.2.1⟩ : AlgebraicSpaces B S hS))
  (ha₁ : subspaceInclusion B S hS T₁' Z₁ ≫ a₁' = a₁ ≫ subspaceInclusion B S hS X₁' W₁)
  (a₂' : T₂' ⟶ X₂')
  (a₂ : (⟨Z₂.1.toFunctor, Z₂.2.1⟩ : AlgebraicSpaces B S hS) ⟶
    (⟨W₂.1.toFunctor, W₂.2.1⟩ : AlgebraicSpaces B S hS))
  (ha₂ : subspaceInclusion B S hS T₂' Z₂ ≫ a₂' = a₂ ≫ subspaceInclusion B S hS X₂' W₂)
  (f' : X₂' ⟶ X₁')
  (f : (⟨W₂.1.toFunctor, W₂.2.1⟩ : AlgebraicSpaces B S hS) ⟶
    (⟨W₁.1.toFunctor, W₁.2.1⟩ : AlgebraicSpaces B S hS))
  (hf : subspaceInclusion B S hS X₂' W₂ ≫ f' = f ≫ subspaceInclusion B S hS X₁' W₁)
  (q₁ : X₁' ⟶ B₁) (q₂ : X₂' ⟶ B₂) (ε : B₂ ⟶ B₁) (hq : f' ≫ q₁ = q₂ ≫ ε)

include hf hq in
/-- The square of differentials of `(f, f')` over `ε : B₂ ⟶ B₁`. -/
theorem comp_comp_eq_of_square_of_over :
    @CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ f
        (subspaceInclusion B S hS X₁' W₁ ≫ q₁) =
      @CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _
        (subspaceInclusion B S hS X₂' W₂ ≫ q₂) ε := by
  rw [← Category.assoc, ← hf, Category.assoc, hq, Category.assoc]

include hq in
/-- The two composites `T₂' ⟶ B₁` of the diagram of [Stacks Project, Tag 0CK8] agree. -/
theorem comp_comp_eq_comp_comp_of_square_of_over (ca' : a₂' ≫ f' = h' ≫ a₁') :
    (h' ≫ a₁') ≫ q₁ = (a₂' ≫ q₂) ≫ ε :=
  (congrArg (· ≫ q₁) ca'.symm).trans
    ((Category.assoc _ _ _).trans ((congrArg (a₂' ≫ ·) hq).trans (Category.assoc _ _ _).symm))

include hq hf in
/-- The postcomposition law of the action (`AlgebraicGeometry.Space.derivationMove_comp`) at
the morphism `(f, f')` over `ε`: `(θ₂ · a₂') ≫ f' = θ'' · (a₂' ≫ f')`. -/
theorem derivationMove_comp_of_square (hT₂ : IsFirstOrderThickening B S hS T₂' Z₂.1)
    (hX₁ : IsFirstOrderThickening B S hS X₁' W₁.1) (hX₂ : IsFirstOrderThickening B S hS X₂' W₂.1)
    (θ₂ : (modulePullback B S hS a₂).obj
        (sheafOfDifferentials B S hS (subspaceInclusion B S hS X₂' W₂ ≫ q₂)) ⟶
      conormalModule B S hS T₂' Z₂) :
    derivationMove B S hS Z₂ W₂ a₂ q₂ hT₂ a₂' ha₂ θ₂ (a₂' ≫ q₂) rfl ≫ f' =
      derivationMove B S hS Z₂ W₁ (@CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ a₂ f) q₁
        hT₂ (a₂' ≫ f') (comp_assoc_of_square_algebraicSpaces B S hS Z₂ W₂ W₁ a₂' a₂ f ha₂ f' hf)
        (postcompDerivationDatum B S hS (subspaceInclusion B S hS X₂' W₂ ≫ q₂)
          (subspaceInclusion B S hS X₁' W₁ ≫ q₁) f ε
          (comp_comp_eq_of_square_of_over B S hS W₁ W₂ f' f hf q₁ q₂ ε hq) a₂
          (conormalModule B S hS T₂' Z₂) θ₂) ((a₂' ≫ q₂) ≫ ε)
        (comp_comp_eq_comp_of_comp_eq B S hS f' q₂ q₁ ε hq a₂' (a₂' ≫ q₂) rfl) :=
  derivationMove_comp B S hS Z₂ W₂ W₁ a₂ f f' hf q₂ q₁ ε
    (comp_comp_eq_of_square_of_over B S hS W₁ W₂ f' f hf q₁ q₂ ε hq) hq hT₂ hX₂ hX₁ a₂' ha₂ θ₂
    (a₂' ≫ q₂) rfl

/-- The precomposition law of the action (`AlgebraicGeometry.Space.comp_derivationMove_of_eq`)
at the morphism `(h, h')`, with the edge `h ≫ a₁` read as `a₂ ≫ f`:
`h' ≫ (θ₁ · a₁') = θ' · (h' ≫ a₁')`. -/
theorem comp_derivationMove_of_square (hT₁ : IsFirstOrderThickening B S hS T₁' Z₁.1)
    (hT₂ : IsFirstOrderThickening B S hS T₂' Z₂.1) (hX₁ : IsFirstOrderThickening B S hS X₁' W₁.1)
    (ca' : a₂' ≫ f' = h' ≫ a₁')
    (ca : @CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ a₂ f =
      @CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ h a₁)
    (θ₁ : (modulePullback B S hS a₁).obj
        (sheafOfDifferentials B S hS (subspaceInclusion B S hS X₁' W₁ ≫ q₁)) ⟶
      conormalModule B S hS T₁' Z₁) :
    h' ≫ derivationMove B S hS Z₁ W₁ a₁ q₁ hT₁ a₁' ha₁ θ₁ (a₁' ≫ q₁) rfl =
      derivationMove B S hS Z₂ W₁ (@CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ a₂ f) q₁
        hT₂ (h' ≫ a₁')
        ((comp_assoc_of_square_algebraicSpaces B S hS Z₂ Z₁ W₁ h' h a₁ hh a₁' ha₁).trans
          (congrArg (· ≫ subspaceInclusion B S hS X₁' W₁) ca.symm))
        ((modulePullbackTriangle B S hS ca.symm).hom.app
          (sheafOfDifferentials B S hS (subspaceInclusion B S hS X₁' W₁ ≫ q₁)) ≫
        (modulePullback B S hS h).map θ₁ ≫ conormalMap B S hS Z₂ Z₁ h' h hh) ((a₂' ≫ q₂) ≫ ε)
        (comp_comp_eq_comp_comp_of_square_of_over B S hS h' a₁' a₂' f' q₁ q₂ ε hq ca') :=
  comp_derivationMove_of_eq B S hS Z₂ Z₁ W₁ h' h a₁ hh q₁ hT₂ hT₁ hX₁ a₁' ha₁
    θ₁ (a₁' ≫ q₁) rfl _ ca.symm _ _ rfl _
    ((Category.assoc _ _ _).symm.trans
      (comp_comp_eq_comp_comp_of_square_of_over B S hS h' a₁' a₂' f' q₁ q₂ ε hq ca')) _

/-- The actions `θ'' · (a₂' ≫ f')` and `θ' · (h' ≫ a₁')` agree when `a₂ ≫ f = h ≫ a₁`,
`a₂' ≫ f' = h' ≫ a₁'` and their data `θ''` and `θ'` are equal. -/
theorem derivationMove_eq_of_square (hT₂ : IsFirstOrderThickening B S hS T₂' Z₂.1)
    (ca' : a₂' ≫ f' = h' ≫ a₁')
    (ca : @CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ a₂ f =
      @CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ h a₁)
    (θ₁ : (modulePullback B S hS a₁).obj
        (sheafOfDifferentials B S hS (subspaceInclusion B S hS X₁' W₁ ≫ q₁)) ⟶
      conormalModule B S hS T₁' Z₁)
    (θ₂ : (modulePullback B S hS a₂).obj
        (sheafOfDifferentials B S hS (subspaceInclusion B S hS X₂' W₂ ≫ q₂)) ⟶
      conormalModule B S hS T₂' Z₂)
    (hθ : (postcompDerivationDatum B S hS (subspaceInclusion B S hS X₂' W₂ ≫ q₂)
          (subspaceInclusion B S hS X₁' W₁ ≫ q₁) f ε
          (comp_comp_eq_of_square_of_over B S hS W₁ W₂ f' f hf q₁ q₂ ε hq) a₂
          (conormalModule B S hS T₂' Z₂) θ₂) =
      ((modulePullbackTriangle B S hS ca.symm).hom.app
          (sheafOfDifferentials B S hS (subspaceInclusion B S hS X₁' W₁ ≫ q₁)) ≫
        (modulePullback B S hS h).map θ₁ ≫ conormalMap B S hS Z₂ Z₁ h' h hh)) :
    derivationMove B S hS Z₂ W₁ (@CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ a₂ f) q₁
        hT₂ (a₂' ≫ f') (comp_assoc_of_square_algebraicSpaces B S hS Z₂ W₂ W₁ a₂' a₂ f ha₂ f' hf)
        (postcompDerivationDatum B S hS (subspaceInclusion B S hS X₂' W₂ ≫ q₂)
          (subspaceInclusion B S hS X₁' W₁ ≫ q₁) f ε
          (comp_comp_eq_of_square_of_over B S hS W₁ W₂ f' f hf q₁ q₂ ε hq) a₂
          (conormalModule B S hS T₂' Z₂) θ₂) ((a₂' ≫ q₂) ≫ ε)
        (comp_comp_eq_comp_of_comp_eq B S hS f' q₂ q₁ ε hq a₂' (a₂' ≫ q₂) rfl) =
      derivationMove B S hS Z₂ W₁ (@CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ a₂ f) q₁
        hT₂ (h' ≫ a₁')
        ((comp_assoc_of_square_algebraicSpaces B S hS Z₂ Z₁ W₁ h' h a₁ hh a₁' ha₁).trans
          (congrArg (· ≫ subspaceInclusion B S hS X₁' W₁) ca.symm))
        ((modulePullbackTriangle B S hS ca.symm).hom.app
          (sheafOfDifferentials B S hS (subspaceInclusion B S hS X₁' W₁ ≫ q₁)) ≫
        (modulePullback B S hS h).map θ₁ ≫ conormalMap B S hS Z₂ Z₁ h' h hh) ((a₂' ≫ q₂) ≫ ε)
        (comp_comp_eq_comp_comp_of_square_of_over B S hS h' a₁' a₂' f' q₁ q₂ ε hq ca') :=
  derivationMove_congr B S hS Z₂ W₁ _ q₁ hT₂ ca' _ _ hθ _ _ _

/-- The equality `(θ₂ · a₂') ≫ f' = h' ≫ (θ₁ · a₁')` of [Stacks Project, Tag 0CK8], for any `θ₂`
whose datum of the postcomposition law is `h^*θ₁` followed by the conormal map of `(h, h')`. -/
theorem derivationMove_comp_of_postcompDerivationDatum_eq
    (hT₁ : IsFirstOrderThickening B S hS T₁' Z₁.1) (hT₂ : IsFirstOrderThickening B S hS T₂' Z₂.1)
    (hX₁ : IsFirstOrderThickening B S hS X₁' W₁.1) (hX₂ : IsFirstOrderThickening B S hS X₂' W₂.1)
    (ca' : a₂' ≫ f' = h' ≫ a₁')
    (ca : @CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ a₂ f =
      @CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ h a₁)
    (θ₁ : (modulePullback B S hS a₁).obj
        (sheafOfDifferentials B S hS (subspaceInclusion B S hS X₁' W₁ ≫ q₁)) ⟶
      conormalModule B S hS T₁' Z₁)
    (θ₂ : (modulePullback B S hS a₂).obj
        (sheafOfDifferentials B S hS (subspaceInclusion B S hS X₂' W₂ ≫ q₂)) ⟶
      conormalModule B S hS T₂' Z₂)
    (hθ : (postcompDerivationDatum B S hS (subspaceInclusion B S hS X₂' W₂ ≫ q₂)
          (subspaceInclusion B S hS X₁' W₁ ≫ q₁) f ε
          (comp_comp_eq_of_square_of_over B S hS W₁ W₂ f' f hf q₁ q₂ ε hq) a₂
          (conormalModule B S hS T₂' Z₂) θ₂) =
      ((modulePullbackTriangle B S hS ca.symm).hom.app
          (sheafOfDifferentials B S hS (subspaceInclusion B S hS X₁' W₁ ≫ q₁)) ≫
        (modulePullback B S hS h).map θ₁ ≫ conormalMap B S hS Z₂ Z₁ h' h hh)) :
    derivationMove B S hS Z₂ W₂ a₂ q₂ hT₂ a₂' ha₂ θ₂ (a₂' ≫ q₂) rfl ≫ f' =
      h' ≫ derivationMove B S hS Z₁ W₁ a₁ q₁ hT₁ a₁' ha₁ θ₁ (a₁' ≫ q₁) rfl :=
  (derivationMove_comp_of_square B S hS Z₂ W₁ W₂ a₂' a₂ ha₂ f' f hf q₁ q₂ ε hq hT₂ hX₁ hX₂ θ₂).trans
    ((derivationMove_eq_of_square B S hS Z₁ Z₂ W₁ W₂ h' h hh a₁' a₁ ha₁ a₂' a₂ ha₂ f' f hf q₁ q₂ ε
      hq hT₂ ca' ca θ₁ θ₂ hθ).trans
      (comp_derivationMove_of_square B S hS Z₁ Z₂ W₁ W₂ h' h hh a₁' a₁ ha₁ a₂' a₂ f' f q₁ q₂ ε hq
        hT₁ hT₂ hX₁ ca' ca θ₁).symm)

/-- **Acting by a derivation commutes with étale localization.**  For a commutative diagram of
first order thickenings `(h, h') : (T₂ ⊂ T₂') ⟶ (T₁ ⊂ T₁')`,
`(a_i, a_i') : (T_i ⊂ T_i') ⟶ (X_i ⊂ X_i')`, `(f, f') : (X₂ ⊂ X₂') ⟶ (X₁ ⊂ X₁')` and a commutative
square `f' ≫ q₁ = q₂ ≫ ε` with `X₂ ⟶ X₁` and `ε : B₂ ⟶ B₁` étale, and for
`θ₁ : a₁^*Ω_{X₁/B₁} ⟶ 𝒞_{T₁/T₁'}` with `θ₂` its étale localization
(`AlgebraicGeometry.Space.etaleLocalizedDerivationDatum`, its last map the conormal map of
`(h, h')`): `(θ₂ · a₂') ≫ f' = h' ≫ (θ₁ · a₁')`, the actions being those of
[Stacks Project, Tag 0CK6] (`AlgebraicGeometry.Space.derivationMove`, `T_i'` over `B_i` through
`a_i'`). -/
@[stacks 0CK8 "the action of Remark 0CK6 is compatible with étale localization: \
(θ₂ · a₂') ≫ f' = h' ≫ (θ₁ · a₁') for θ₂ the composite a₂^*Ω_{X₂/B₂} = h^*a₁^*Ω_{X₁/B₁} → \
h^*C_{T₁/T₁'} → C_{T₂/T₂'}, the equality sign the identification of 04CU"]
theorem derivationMove_comp_of_etale
    (hT₁ : IsFirstOrderThickening B S hS T₁' Z₁.1) (hT₂ : IsFirstOrderThickening B S hS T₂' Z₂.1)
    (hX₁ : IsFirstOrderThickening B S hS X₁' W₁.1) (hX₂ : IsFirstOrderThickening B S hS X₂' W₂.1)
    (ca' : a₂' ≫ f' = h' ≫ a₁') (ca : @CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ a₂ f =
      @CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ h a₁)
    (hfet : IsEtale B S hS f.hom) (hεet : IsEtale B S hS ε.hom)
    (θ₁ : (modulePullback B S hS a₁).obj
        (sheafOfDifferentials B S hS (subspaceInclusion B S hS X₁' W₁ ≫ q₁)) ⟶
      conormalModule B S hS T₁' Z₁) :
    derivationMove B S hS Z₂ W₂ a₂ q₂ hT₂ a₂' ha₂
        (etaleLocalizedDerivationDatum B S hS (subspaceInclusion B S hS X₂' W₂ ≫ q₂)
          (subspaceInclusion B S hS X₁' W₁ ≫ q₁) f ε
          (comp_comp_eq_of_square_of_over B S hS W₁ W₂ f' f hf q₁ q₂ ε hq) a₂ h a₁ ca.symm
          (isIso_sheafOfDifferentialsMap_of_isEtale B S hS
            (subspaceInclusion B S hS X₁' W₁ ≫ q₁) f (subspaceInclusion B S hS X₂' W₂ ≫ q₂) ε
            hfet hεet (comp_comp_eq_of_square_of_over B S hS W₁ W₂ f' f hf q₁ q₂ ε hq))
          (conormalModule B S hS T₁' Z₁) (conormalModule B S hS T₂' Z₂) θ₁
          (conormalMap B S hS Z₂ Z₁ h' h hh)) (a₂' ≫ q₂) rfl ≫ f' =
      h' ≫ derivationMove B S hS Z₁ W₁ a₁ q₁ hT₁ a₁' ha₁ θ₁ (a₁' ≫ q₁) rfl :=
  derivationMove_comp_of_postcompDerivationDatum_eq B S hS Z₁ Z₂ W₁ W₂ h' h hh a₁' a₁ ha₁ a₂' a₂
    ha₂ f' f hf q₁ q₂ ε hq hT₁ hT₂ hX₁ hX₂ ca' ca θ₁ _
    (postcompDerivationDatum_etaleLocalizedDerivationDatum B S hS ..)

end EtaleLocalization

end AlgebraicGeometry.Space

end
