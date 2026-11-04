module

public import StacksFrontier.AlgebraicGeometry.Spaces.DeformationLiftActionSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.DerivationMovePrecomposition

/-!
# The action of [Stacks Project, Tag 061C] commutes with restriction

The action `θ · a'` of the acting sheaf
`SheafHom_{𝒪_X}(a^*Ω_{Y/T}, 𝒞_{X/X'})` on the sheaf of lifts of [Stacks Project, Tag 061B]
(`AlgebraicGeometry.Space.conormalLiftSheafAddAction`) is compatible with the restriction maps
of the two sheaves: for a morphism `k : V' ⟶ U'` of the spaces-étale site of `X'`,
`(θ · a')|_{V'} = θ|_{V'} · a'|_{V'}`.

## Main results

* `AlgebraicGeometry.Space.comp_derivationMove_restriction`: the general form, at a morphism
  `ψ : W₂ ⟶ W` of algebraic spaces over `X'`.
* `AlgebraicGeometry.Space.conormalLiftAction_map`: the action of [Stacks Project, Tag 061C]
  commutes with the restriction maps.
* `AlgebraicGeometry.Space.comp_derivationMove_restriction_of_spaces`: the same, with the inverse
  images, the projections and the modules handed over as variables fixed by equations.

## References

* [Stacks Project, Tag 061C](https://stacks.math.columbia.edu/tag/061C)
* [Stacks Project, Tag 0CK6](https://stacks.math.columbia.edu/tag/0CK6)
* [Stacks Project, Tag 04G2](https://stacks.math.columbia.edu/tag/04G2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)

-- Unfolding the inverse image to its construction does not terminate, and is never needed here.
attribute [local irreducible] modulePullback

/-- **The precomposition law of the action of [Stacks Project, Tag 0CK6], with the composite
edge and the restricted section handed over in arguments.**  This is
`AlgebraicGeometry.Space.comp_derivationMove` with the edge `h ≫ e₀` of the restricted morphism
of thickenings replaced by any `e₀'` equal to it, the restricted section read through the
comparison of Stacks 03LU indexed by that equation
(`AlgebraicGeometry.Space.modulePullbackTriangle`), and the structure morphism to `T` replaced by
any `p'` equal to `h' ≫ p`. -/
theorem comp_derivationMove_of_eq {X₂ X W T : AlgebraicSpaces C S hS}
    (Z₂ : ClosedSubspaces C S hS X₂.1) (Z : ClosedSubspaces C S hS X.1)
    (W₀ : ClosedSubspaces C S hS W.1) (h' : X₂ ⟶ X)
    (h : (⟨Z₂.1.toFunctor, Z₂.2.1⟩ : AlgebraicSpaces C S hS) ⟶
      (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS))
    (e₀ : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS) ⟶
      (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces C S hS))
    (hsq : subspaceInclusion C S hS X₂ Z₂ ≫ h' = h ≫ subspaceInclusion C S hS X Z)
    (q : W ⟶ T)
    (hZ₂ : IsFirstOrderThickening C S hS X₂ Z₂.1) (hZ : IsFirstOrderThickening C S hS X Z.1)
    (hW : IsFirstOrderThickening C S hS W W₀.1) (c : X ⟶ W)
    (hc : subspaceInclusion C S hS X Z ≫ c = e₀ ≫ subspaceInclusion C S hS W W₀)
    (θ : (modulePullback C S hS e₀).obj
        (sheafOfDifferentials C S hS (subspaceInclusion C S hS W W₀ ≫ q)) ⟶
      conormalModule C S hS X Z)
    (p : X ⟶ T) (hcq : c ≫ q = p)
    (e₀' : (⟨Z₂.1.toFunctor, Z₂.2.1⟩ : AlgebraicSpaces C S hS) ⟶
      (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces C S hS))
    (hfc : @CategoryStruct.comp (AlgebraicSpaces C S hS) _ _ _ _ h e₀ = e₀')
    (hc' : subspaceInclusion C S hS X₂ Z₂ ≫ h' ≫ c = e₀' ≫ subspaceInclusion C S hS W W₀)
    (θ' : (modulePullback C S hS e₀').obj
        (sheafOfDifferentials C S hS (subspaceInclusion C S hS W W₀ ≫ q)) ⟶
      conormalModule C S hS X₂ Z₂)
    (hθ' : θ' = (modulePullbackTriangle C S hS hfc).hom.app
        (sheafOfDifferentials C S hS (subspaceInclusion C S hS W W₀ ≫ q)) ≫
          (modulePullback C S hS h).map θ ≫ conormalMap C S hS Z₂ Z h' h hsq)
    (p' : X₂ ⟶ T) (hp : h' ≫ p = p') (hcq' : (h' ≫ c) ≫ q = p') :
    h' ≫ derivationMove C S hS Z W₀ e₀ q hZ c hc θ p hcq =
      derivationMove C S hS Z₂ W₀ e₀' q hZ₂ (h' ≫ c) hc' θ' p' hcq' := by
  subst hfc hp hθ'
  rw [modulePullbackTriangle_rfl_hom_app]
  exact comp_derivationMove C S hS Z₂ Z W₀ h' h e₀ hsq q hZ₂ hZ hW c hc θ p hcq

/-- The comparison of an inverse image with an iterated inverse image along a factorization is
the comparison `AlgebraicGeometry.Space.modulePullbackTriangle` indexed by the same equation. -/
theorem pullbackComparison_hom_eq_modulePullbackTriangle_hom_app {A P P' : AlgebraicSpaces C S hS}
    (g : P' ⟶ P) (p : P ⟶ A) (v : P' ⟶ A) (hv : g ≫ p = v) (M : Modules.{u, u} C S hS A.1 A.2) :
    (QuasiCoherentDescent.pullbackComparison C S hS g p v hv M).hom =
      (modulePullbackTriangle C S hS hv).hom.app M := by
  subst hv
  rw [QuasiCoherentDescent.pullbackComparison_rfl, modulePullbackTriangle_rfl_hom_app]
  rfl

/-- **The comparison of Stacks 03LU at a three-step factorization.**  For `r ≫ p = q`, the
comparison along `q ≫ α` followed by the comparison along `r ≫ p = q` and by the inverse image
along `r` of the comparison along `p ≫ α` is the comparison indexed by `r ≫ p ≫ α = q ≫ α`. -/
theorem modulePullbackCompIso_inv_pullbackComparison_map_hom
    {Z₂s Z₁s ZGs YHs : AlgebraicSpaces C S hS}
    (r : Z₂s ⟶ Z₁s) (p : Z₁s ⟶ ZGs) (q : Z₂s ⟶ ZGs) (α : ZGs ⟶ YHs)
    (hq : r ≫ p = q) (hqα : r ≫ p ≫ α = q ≫ α) (M : Modules.{u, u} C S hS YHs.1 YHs.2) :
    (modulePullbackCompIso C S hS q α).inv.app M ≫
        (QuasiCoherentDescent.pullbackComparison C S hS r p q hq
          ((modulePullback C S hS α).obj M)).hom ≫
        (modulePullback C S hS r).map ((modulePullbackCompIso C S hS p α).hom.app M) =
      (modulePullbackTriangle C S hS hqα).hom.app M := by
  have h := modulePullbackTriangle_hom_app_compIso_inv_app C S hS Z₂s Z₁s ZGs YHs r p q α hq hqα M
  rw [pullbackComparison_hom_eq_modulePullbackTriangle_hom_app, ← Category.assoc, ← h,
    Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  exact Category.comp_id _

/-- **A restricted section read through two pairs of comparisons.**  For `g ≫ p = v`, a
morphism `cU ≫ θ ≫ eU⁻¹` of inverse images along `p`, restricted along `g`, and conjugated by
`cV` and `eV`, is `t ≫ g^*θ ≫ γ` as soon as the two outer comparisons are `t` and `γ` on the two
sides. -/
theorem comp_restrictForm_comp_eq {A P P' : AlgebraicSpaces C S hS} (g : P' ⟶ P) (p : P ⟶ A)
    (v : P' ⟶ A) (hv : g ≫ p = v) {M N : Modules.{u, u} C S hS A.1 A.2}
    {Mp Cφ : Modules.{u, u} C S hS P.1 P.2} {Ω₂ C₂ : Modules.{u, u} C S hS P'.1 P'.2}
    (cV : Ω₂ ⟶ (modulePullback C S hS v).obj M) (cU : (modulePullback C S hS p).obj M ⟶ Mp)
    (θ : Mp ⟶ Cφ) (eU : (modulePullback C S hS p).obj N ≅ Cφ)
    (eV : (modulePullback C S hS v).obj N ≅ C₂)
    (t : Ω₂ ⟶ (modulePullback C S hS g).obj Mp)
    (γ : (modulePullback C S hS g).obj Cφ ⟶ C₂)
    (H1 : cV ≫ (QuasiCoherentDescent.pullbackComparison C S hS g p v hv M).hom ≫
      (modulePullback C S hS g).map cU = t)
    (H2 : eV.hom = (QuasiCoherentDescent.pullbackComparison C S hS g p v hv N).hom ≫
      (modulePullback C S hS g).map eU.hom ≫ γ) :
    cV ≫ QuasiCoherentDescent.restrictForm C S hS g p v hv (cU ≫ θ ≫ eU.inv) ≫ eV.hom =
      t ≫ (modulePullback C S hS g).map θ ≫ γ := by
  rw [QuasiCoherentDescent.restrictForm_eq, H2, ← H1]
  simp only [QuasiCoherentDescent.factorForm, Functor.map_comp, Category.assoc,
    Iso.inv_hom_id_assoc, Iso.map_inv_hom_id_assoc]

/-- **A restricted section of `SheafHom(α^*M, N)` read through Stacks 03LU.**  For `r ≫ p = q`,
a map `θ : (p ≫ α)^*M ⟶ Cφ`, read as a map `p^*α^*M ⟶ p^*N` through Stacks 03LU and `eU`,
restricted along `r` and read back through Stacks 03LU and `eV`, is the comparison indexed by
`r ≫ p ≫ α = q ≫ α`, followed by `r^*θ` and by `γ`, as soon as `eV` is the comparison along
`r ≫ p = q`, followed by `r^*eU` and by `γ`. -/
theorem compIso_inv_restrictForm_comp_eq {Z₂s Z₁s ZGs YHs : AlgebraicSpaces C S hS}
    (r : Z₂s ⟶ Z₁s) (p : Z₁s ⟶ ZGs) (q : Z₂s ⟶ ZGs) (α : ZGs ⟶ YHs)
    (hq : r ≫ p = q) (hqα : r ≫ p ≫ α = q ≫ α) (M : Modules.{u, u} C S hS YHs.1 YHs.2)
    {N : Modules.{u, u} C S hS ZGs.1 ZGs.2} {Cφ : Modules.{u, u} C S hS Z₁s.1 Z₁s.2}
    {C₂ : Modules.{u, u} C S hS Z₂s.1 Z₂s.2}
    (θ : (modulePullback C S hS (p ≫ α)).obj M ⟶ Cφ)
    (eU : (modulePullback C S hS p).obj N ≅ Cφ) (eV : (modulePullback C S hS q).obj N ≅ C₂)
    (γ : (modulePullback C S hS r).obj Cφ ⟶ C₂)
    (H2 : eV.hom = (QuasiCoherentDescent.pullbackComparison C S hS r p q hq N).hom ≫
      (modulePullback C S hS r).map eU.hom ≫ γ) :
    (modulePullbackCompIso C S hS q α).inv.app M ≫
        QuasiCoherentDescent.restrictForm C S hS r p q hq
          ((modulePullbackCompIso C S hS p α).hom.app M ≫ θ ≫ eU.inv) ≫ eV.hom =
      (modulePullbackTriangle C S hS hqα).hom.app M ≫ (modulePullback C S hS r).map θ ≫ γ := by
  exact comp_restrictForm_comp_eq C S hS r p q hq _ _ θ eU eV _ γ
    (modulePullbackCompIso_inv_pullbackComparison_map_hom C S hS r p q α hq hqα M) H2

/-- **The action of [Stacks Project, Tag 0CK6] commutes with restriction.**  Let `Z ⊂ X'` and
`ZH ⊂ Y'` be closed subspaces, `ZH ⊂ Y'` a first order thickening over `T`, let
`φ : W ⟶ X'`, `ψ : W₂ ⟶ W`, `φ₂ = ψ ≫ φ`, and let `ZU ⊂ W`, `ZV ⊂ W₂` be first order
thickenings lying over `Z` along `pU`, `pV`, with a morphism `r : ZV ⟶ ZU` over `ψ` and over
`Z`.  Let `(pU ≫ α, c)` be a morphism of thickenings `(ZU ⊂ W) ⟶ (ZH ⊂ Y')` over `T` and
`θ : (pU ≫ α)^*Ω_{ZH/T} ⟶ 𝒞_{ZU/W}`.  Let `eU`, `eV` be isomorphisms whose forward maps are the
canonical maps `pU^*𝒞_{Z/X'} ⟶ 𝒞_{ZU/W}` and `pV^*𝒞_{Z/X'} ⟶ 𝒞_{ZV/W₂}` of
[Stacks Project, Tag 04CP].  If `θ₂` is the restriction of `θ` along `r` — `θ` read as a map
`pU^*α^*Ω ⟶ pU^*𝒞_{Z/X'}` through Stacks 03LU and `eU`, restricted along `r` and read back through
Stacks 03LU and `eV` — then `ψ ≫ (θ · c) = θ₂ · (ψ ≫ c)`. -/
theorem comp_derivationMove_restriction {X' Y' T W W₂ : AlgebraicSpaces C S hS}
    (Z : ClosedSubspaces C S hS X'.1) (ZH : ClosedSubspaces C S hS Y'.1)
    (ZU : ClosedSubspaces C S hS W.1) (ZV : ClosedSubspaces C S hS W₂.1)
    (ψ : W₂ ⟶ W) (φ : W ⟶ X') (φ₂ : W₂ ⟶ X') (hφ : ψ ≫ φ = φ₂)
    (pU : (⟨ZU.1.toFunctor, ZU.2.1⟩ : AlgebraicSpaces C S hS) ⟶ ⟨Z.1.toFunctor, Z.2.1⟩)
    (pV : (⟨ZV.1.toFunctor, ZV.2.1⟩ : AlgebraicSpaces C S hS) ⟶ ⟨Z.1.toFunctor, Z.2.1⟩)
    (hsqU : subspaceInclusion C S hS W ZU ≫ φ = pU ≫ subspaceInclusion C S hS X' Z)
    (hsqV : subspaceInclusion C S hS W₂ ZV ≫ φ₂ = pV ≫ subspaceInclusion C S hS X' Z)
    (α : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS) ⟶
      (⟨ZH.1.toFunctor, ZH.2.1⟩ : AlgebraicSpaces C S hS))
    (q : Y' ⟶ T) (pX' : X' ⟶ T)
    (hZU : IsFirstOrderThickening C S hS W ZU.1) (hZV : IsFirstOrderThickening C S hS W₂ ZV.1)
    (hW : IsFirstOrderThickening C S hS Y' ZH.1)
    (r : (⟨ZV.1.toFunctor, ZV.2.1⟩ : AlgebraicSpaces C S hS) ⟶ ⟨ZU.1.toFunctor, ZU.2.1⟩)
    (hr : subspaceInclusion C S hS W₂ ZV ≫ ψ = r ≫ subspaceInclusion C S hS W ZU)
    (hpr : r ≫ pU = pV)
    (eU : (modulePullback C S hS pU).obj (conormalModule C S hS X' Z) ≅
      conormalModule C S hS W ZU)
    (heU : eU.hom = conormalMap C S hS ZU Z φ pU hsqU)
    (eV : (modulePullback C S hS pV).obj (conormalModule C S hS X' Z) ≅
      conormalModule C S hS W₂ ZV)
    (heV : eV.hom = conormalMap C S hS ZV Z φ₂ pV hsqV)
    (c : W ⟶ Y')
    (hc : subspaceInclusion C S hS W ZU ≫ c =
      (@CategoryStruct.comp (AlgebraicSpaces C S hS) _ _ _ _ pU α) ≫
      subspaceInclusion C S hS Y' ZH)
    (hcq : c ≫ q = φ ≫ pX')
    (hc₂ : subspaceInclusion C S hS W₂ ZV ≫ ψ ≫ c =
      (@CategoryStruct.comp (AlgebraicSpaces C S hS) _ _ _ _ pV α) ≫
      subspaceInclusion C S hS Y' ZH)
    (hcq₂ : (ψ ≫ c) ≫ q = φ₂ ≫ pX')
    (θ : (modulePullback C S hS
        (@CategoryStruct.comp (AlgebraicSpaces C S hS) _ _ _ _ pU α)).obj
        (sheafOfDifferentials C S hS (subspaceInclusion C S hS Y' ZH ≫ q)) ⟶
      conormalModule C S hS W ZU)
    (θ₂ : (modulePullback C S hS
        (@CategoryStruct.comp (AlgebraicSpaces C S hS) _ _ _ _ pV α)).obj
        (sheafOfDifferentials C S hS (subspaceInclusion C S hS Y' ZH ≫ q)) ⟶
      conormalModule C S hS W₂ ZV)
    (hθ₂ : θ₂ = Iso.homCongr ((modulePullbackCompIso C S hS pV α).app
          (sheafOfDifferentials C S hS (subspaceInclusion C S hS Y' ZH ≫ q))) eV
        (QuasiCoherentDescent.restrictForm C S hS r pU pV hpr
          ((Iso.homCongr ((modulePullbackCompIso C S hS pU α).app
            (sheafOfDifferentials C S hS (subspaceInclusion C S hS Y' ZH ≫ q))) eU).symm θ))) :
    ψ ≫ derivationMove C S hS ZU ZH
        (@CategoryStruct.comp (AlgebraicSpaces C S hS) _ _ _ _ pU α) q hZU c hc θ (φ ≫ pX') hcq =
      derivationMove C S hS ZV ZH
        (@CategoryStruct.comp (AlgebraicSpaces C S hS) _ _ _ _ pV α) q hZV (ψ ≫ c) hc₂ θ₂
        (φ₂ ≫ pX') hcq₂ := by
  subst hφ
  have hfc : @CategoryStruct.comp (AlgebraicSpaces C S hS) _ _ _ _ r
      (@CategoryStruct.comp (AlgebraicSpaces C S hS) _ _ _ _ pU α) =
        (@CategoryStruct.comp (AlgebraicSpaces C S hS) _ _ _ _ pV α) :=
    (Category.assoc _ _ _).symm.trans (congrArg (· ≫ α) hpr)
  refine comp_derivationMove_of_eq C S hS ZV ZU ZH ψ r
    (@CategoryStruct.comp (AlgebraicSpaces C S hS) _ _ _ _ pU α) hr q hZV hZU hW c hc θ
    (φ ≫ pX') hcq
    (@CategoryStruct.comp (AlgebraicSpaces C S hS) _ _ _ _ pV α) hfc hc₂ θ₂ ?_ ((ψ ≫ φ) ≫ pX')
    (Category.assoc _ _ _).symm hcq₂
  have H2 : eV.hom = (QuasiCoherentDescent.pullbackComparison C S hS r pU pV hpr
      (conormalModule C S hS X' Z)).hom ≫ (modulePullback C S hS r).map eU.hom ≫
        conormalMap C S hS ZV ZU ψ r hr := by
    rw [heV, heU, pullbackComparison_hom_eq_modulePullbackTriangle_hom_app]
    exact conormalMap_comp_triangle C S hS ψ φ ZV ZU Z r pU hr hsqU pV hpr hsqV
  rw [hθ₂, Iso.homCongr_apply, Iso.homCongr_symm, Iso.homCongr_apply, Iso.symm_inv,
    Iso.symm_hom, Iso.app_inv, Iso.app_hom]
  exact compIso_inv_restrictForm_comp_eq C S hS r pU pV α hpr hfc
    (sheafOfDifferentials C S hS (subspaceInclusion C S hS Y' ZH ≫ q)) θ eU eV
    (conormalMap C S hS ZV ZU ψ r hr) H2

/-- A functor to types with its objects replaced along a family of bijections acts on morphisms
by conjugating with them. -/
theorem copyObj_toIso_map_apply {𝒞 : Type*} [Category 𝒞] (F : 𝒞 ⥤ Type (u + 1))
    (obj : 𝒞 → Type (u + 1)) (e : ∀ X, F.obj X ≃ obj X) {X Y : 𝒞} (f : X ⟶ Y) (x : obj X) :
    (F.copyObj obj fun X ↦ (e X).toIso).map f x = e Y (F.map f ((e X).symm x)) :=
  rfl

/-- A functor to types with its objects replaced along a family of isomorphisms acts on morphisms
by conjugating with them. -/
theorem copyObj_map_apply {𝒞 : Type*} [Category 𝒞] (F : 𝒞 ⥤ Type (u + 1))
    (obj : 𝒞 → Type (u + 1)) (i : ∀ X, F.obj X ≅ obj X) {X Y : 𝒞} (f : X ⟶ Y) (x : obj X) :
    (F.copyObj obj i).map f x = (i Y).hom (F.map f ((i X).inv x)) :=
  rfl

/-- An element of the target of a family of isomorphisms of types is the image of its preimage. -/
theorem iso_hom_inv_apply_eq {𝒞 : Type*} [Category 𝒞] (F : 𝒞 ⥤ Type (u + 1))
    (obj : 𝒞 → Type (u + 1)) (i : ∀ X, F.obj X ≅ obj X) (X : 𝒞) (x : obj X) :
    x = (i X).hom ((i X).inv x) :=
  (Iso.inv_hom_id_apply (i X) x).symm

/-- A functor to types with its objects replaced along a family of isomorphisms sends the image of
an element under the isomorphism to the image of its image. -/
theorem copyObj_map_hom_apply {𝒞 : Type*} [Category 𝒞] (F : 𝒞 ⥤ Type (u + 1))
    (obj : 𝒞 → Type (u + 1)) (i : ∀ X, F.obj X ≅ obj X) {X Y : 𝒞} (f : X ⟶ Y) (x : F.obj X) :
    (F.copyObj obj i).map f ((i X).hom x) = (i Y).hom (F.map f x) := by
  rw [copyObj_map_apply, Iso.hom_inv_id_apply]

/-- A composite of functors into types acts on an element as the second functor at the image of
the morphism under the first. -/
theorem comp_map_apply_eq {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] (F : 𝒞 ⥤ 𝒟)
    (G : 𝒟 ⥤ Type (u + 1)) {X Y : 𝒞} (f : X ⟶ Y) (x : G.obj (F.obj X)) :
    (F ⋙ G).map f x = G.map (F.map f) x :=
  rfl

/-- `AlgebraicGeometry.Space.comp_derivationMove_restriction` with the section `θ` over `U`
presented as the reading `θ = (θ'' read through Stacks 03LU and eU)` of a section `θ''` of
`SheafHom(α^*Ω, 𝒞_{X'/Z})` over `pU`, and its restriction `θ₂` the reading of the restriction of
`θ''` along `r`. -/
theorem comp_derivationMove_restriction_of_eq {X' Y' T W W₂ : AlgebraicSpaces C S hS}
    (Z : ClosedSubspaces C S hS X'.1) (ZH : ClosedSubspaces C S hS Y'.1)
    (ZU : ClosedSubspaces C S hS W.1) (ZV : ClosedSubspaces C S hS W₂.1)
    (ψ : W₂ ⟶ W) (φ : W ⟶ X') (φ₂ : W₂ ⟶ X') (hφ : ψ ≫ φ = φ₂)
    (pU : (⟨ZU.1.toFunctor, ZU.2.1⟩ : AlgebraicSpaces C S hS) ⟶ ⟨Z.1.toFunctor, Z.2.1⟩)
    (pV : (⟨ZV.1.toFunctor, ZV.2.1⟩ : AlgebraicSpaces C S hS) ⟶ ⟨Z.1.toFunctor, Z.2.1⟩)
    (hsqU : subspaceInclusion C S hS W ZU ≫ φ = pU ≫ subspaceInclusion C S hS X' Z)
    (hsqV : subspaceInclusion C S hS W₂ ZV ≫ φ₂ = pV ≫ subspaceInclusion C S hS X' Z)
    (α : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS) ⟶
      (⟨ZH.1.toFunctor, ZH.2.1⟩ : AlgebraicSpaces C S hS))
    (q : Y' ⟶ T) (pX' : X' ⟶ T)
    (hZU : IsFirstOrderThickening C S hS W ZU.1) (hZV : IsFirstOrderThickening C S hS W₂ ZV.1)
    (hW : IsFirstOrderThickening C S hS Y' ZH.1)
    (r : (⟨ZV.1.toFunctor, ZV.2.1⟩ : AlgebraicSpaces C S hS) ⟶ ⟨ZU.1.toFunctor, ZU.2.1⟩)
    (hr : subspaceInclusion C S hS W₂ ZV ≫ ψ = r ≫ subspaceInclusion C S hS W ZU)
    (hpr : r ≫ pU = pV)
    (eU : (modulePullback C S hS pU).obj (conormalModule C S hS X' Z) ≅
      conormalModule C S hS W ZU)
    (heU : eU.hom = conormalMap C S hS ZU Z φ pU hsqU)
    (eV : (modulePullback C S hS pV).obj (conormalModule C S hS X' Z) ≅
      conormalModule C S hS W₂ ZV)
    (heV : eV.hom = conormalMap C S hS ZV Z φ₂ pV hsqV)
    (c : W ⟶ Y')
    (hc : subspaceInclusion C S hS W ZU ≫ c =
      (@CategoryStruct.comp (AlgebraicSpaces C S hS) _ _ _ _ pU α) ≫
        subspaceInclusion C S hS Y' ZH)
    (hcq : c ≫ q = φ ≫ pX')
    (hc₂ : subspaceInclusion C S hS W₂ ZV ≫ ψ ≫ c =
      (@CategoryStruct.comp (AlgebraicSpaces C S hS) _ _ _ _ pV α) ≫
        subspaceInclusion C S hS Y' ZH)
    (hcq₂ : (ψ ≫ c) ≫ q = φ₂ ≫ pX')
    (θ'' : (modulePullback C S hS pU).obj ((modulePullback C S hS α).obj
        (sheafOfDifferentials C S hS (subspaceInclusion C S hS Y' ZH ≫ q))) ⟶
      (modulePullback C S hS pU).obj (conormalModule C S hS X' Z))
    (θ : (modulePullback C S hS
        (@CategoryStruct.comp (AlgebraicSpaces C S hS) _ _ _ _ pU α)).obj
        (sheafOfDifferentials C S hS (subspaceInclusion C S hS Y' ZH ≫ q)) ⟶
      conormalModule C S hS W ZU)
    (hθ : θ = Iso.homCongr ((modulePullbackCompIso C S hS pU α).app
          (sheafOfDifferentials C S hS (subspaceInclusion C S hS Y' ZH ≫ q))) eU θ'')
    (θ₂ : (modulePullback C S hS
        (@CategoryStruct.comp (AlgebraicSpaces C S hS) _ _ _ _ pV α)).obj
        (sheafOfDifferentials C S hS (subspaceInclusion C S hS Y' ZH ≫ q)) ⟶
      conormalModule C S hS W₂ ZV)
    (hθ₂ : θ₂ = Iso.homCongr ((modulePullbackCompIso C S hS pV α).app
          (sheafOfDifferentials C S hS (subspaceInclusion C S hS Y' ZH ≫ q))) eV
        (QuasiCoherentDescent.restrictForm C S hS r pU pV hpr θ'')) :
    ψ ≫ derivationMove C S hS ZU ZH
        (@CategoryStruct.comp (AlgebraicSpaces C S hS) _ _ _ _ pU α) q hZU c hc θ (φ ≫ pX') hcq =
      derivationMove C S hS ZV ZH
        (@CategoryStruct.comp (AlgebraicSpaces C S hS) _ _ _ _ pV α) q hZV (ψ ≫ c) hc₂ θ₂
        (φ₂ ≫ pX') hcq₂ := by
  subst hθ
  refine comp_derivationMove_restriction C S hS Z ZH ZU ZV ψ φ φ₂ hφ pU pV hsqU hsqV α q pX' hZU
    hZV hW r hr hpr eU heU eV heV c hc hcq hc₂ hcq₂ _ θ₂ ?_
  rw [hθ₂, Equiv.symm_apply_apply]

/-- `AlgebraicGeometry.Space.comp_derivationMove_restriction_of_eq` with the two inverse images
of `Z` handed over as algebraic spaces `ZUs`, `ZVs` of their own, fixed by equations of spaces, and
the readings of the sections, the projections, the restriction edge, the conormal modules and
their identifications carried over them, fixed by heterogeneous equalities. -/
theorem comp_derivationMove_restriction_of_spaces {X' Y' T W W₂ : AlgebraicSpaces C S hS}
    (Z : ClosedSubspaces C S hS X'.1) (ZH : ClosedSubspaces C S hS Y'.1)
    (ZU : ClosedSubspaces C S hS W.1) (ZV : ClosedSubspaces C S hS W₂.1)
    (ψ : W₂ ⟶ W) (φ : W ⟶ X') (φ₂ : W₂ ⟶ X') (hφ : ψ ≫ φ = φ₂)
    (pU : (⟨ZU.1.toFunctor, ZU.2.1⟩ : AlgebraicSpaces C S hS) ⟶ ⟨Z.1.toFunctor, Z.2.1⟩)
    (pV : (⟨ZV.1.toFunctor, ZV.2.1⟩ : AlgebraicSpaces C S hS) ⟶ ⟨Z.1.toFunctor, Z.2.1⟩)
    (hsqU : subspaceInclusion C S hS W ZU ≫ φ = pU ≫ subspaceInclusion C S hS X' Z)
    (hsqV : subspaceInclusion C S hS W₂ ZV ≫ φ₂ = pV ≫ subspaceInclusion C S hS X' Z)
    (α : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS) ⟶
      (⟨ZH.1.toFunctor, ZH.2.1⟩ : AlgebraicSpaces C S hS))
    (q : Y' ⟶ T) (pX' : X' ⟶ T)
    (hZU : IsFirstOrderThickening C S hS W ZU.1) (hZV : IsFirstOrderThickening C S hS W₂ ZV.1)
    (hW : IsFirstOrderThickening C S hS Y' ZH.1)
    (r : (⟨ZV.1.toFunctor, ZV.2.1⟩ : AlgebraicSpaces C S hS) ⟶ ⟨ZU.1.toFunctor, ZU.2.1⟩)
    (hr : subspaceInclusion C S hS W₂ ZV ≫ ψ = r ≫ subspaceInclusion C S hS W ZU)
    (hpr : r ≫ pU = pV)
    (eU : (modulePullback C S hS pU).obj (conormalModule C S hS X' Z) ≅
      conormalModule C S hS W ZU)
    (heU : eU.hom = conormalMap C S hS ZU Z φ pU hsqU)
    (eV : (modulePullback C S hS pV).obj (conormalModule C S hS X' Z) ≅
      conormalModule C S hS W₂ ZV)
    (heV : eV.hom = conormalMap C S hS ZV Z φ₂ pV hsqV)
    (c : W ⟶ Y')
    (hc : subspaceInclusion C S hS W ZU ≫ c =
      (@CategoryStruct.comp (AlgebraicSpaces C S hS) _ _ _ _ pU α) ≫
        subspaceInclusion C S hS Y' ZH)
    (hcq : c ≫ q = φ ≫ pX')
    (hc₂ : subspaceInclusion C S hS W₂ ZV ≫ ψ ≫ c =
      (@CategoryStruct.comp (AlgebraicSpaces C S hS) _ _ _ _ pV α) ≫
        subspaceInclusion C S hS Y' ZH)
    (hcq₂ : (ψ ≫ c) ≫ q = φ₂ ≫ pX')
    (θ : (modulePullback C S hS
        (@CategoryStruct.comp (AlgebraicSpaces C S hS) _ _ _ _ pU α)).obj
        (sheafOfDifferentials C S hS (subspaceInclusion C S hS Y' ZH ≫ q)) ⟶
      conormalModule C S hS W ZU)
    (θ₂ : (modulePullback C S hS
        (@CategoryStruct.comp (AlgebraicSpaces C S hS) _ _ _ _ pV α)).obj
        (sheafOfDifferentials C S hS (subspaceInclusion C S hS Y' ZH ≫ q)) ⟶
      conormalModule C S hS W₂ ZV)
    (ZUs ZVs ZGs ZHs : AlgebraicSpaces C S hS)
    (hZUs : (⟨ZU.1.toFunctor, ZU.2.1⟩ : AlgebraicSpaces C S hS) = ZUs)
    (hZVs : (⟨ZV.1.toFunctor, ZV.2.1⟩ : AlgebraicSpaces C S hS) = ZVs)
    (hZGs : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS) = ZGs)
    (hZHs : (⟨ZH.1.toFunctor, ZH.2.1⟩ : AlgebraicSpaces C S hS) = ZHs)
    (αs : ZGs ⟶ ZHs) (hαs : HEq αs α)
    (Ωs : Modules.{u, u} C S hS ZHs.1 ZHs.2)
    (hΩs : HEq Ωs (sheafOfDifferentials C S hS (subspaceInclusion C S hS Y' ZH ≫ q)))
    (Cs : Modules.{u, u} C S hS ZGs.1 ZGs.2) (hCs : HEq Cs (conormalModule C S hS X' Z))
    (pUs : ZUs ⟶ ZGs) (hpUs : HEq pUs pU) (pVs : ZVs ⟶ ZGs) (hpVs : HEq pVs pV)
    (rs : ZVs ⟶ ZUs) (hrs : HEq rs r) (hprs : rs ≫ pUs = pVs)
    (NU : Modules.{u, u} C S hS ZUs.1 ZUs.2) (hNU : HEq NU (conormalModule C S hS W ZU))
    (NV : Modules.{u, u} C S hS ZVs.1 ZVs.2) (hNV : HEq NV (conormalModule C S hS W₂ ZV))
    (eUs : (modulePullback C S hS pUs).obj Cs ≅ NU) (heUs : HEq eUs eU)
    (eVs : (modulePullback C S hS pVs).obj Cs ≅ NV) (heVs : HEq eVs eV)
    (θ'' : (modulePullback C S hS pUs).obj ((modulePullback C S hS αs).obj Ωs) ⟶
      (modulePullback C S hS pUs).obj Cs)
    (hθ : HEq θ (Iso.homCongr ((modulePullbackCompIso C S hS pUs αs).app Ωs) eUs θ''))
    (hθ₂ : HEq θ₂ (Iso.homCongr ((modulePullbackCompIso C S hS pVs αs).app Ωs) eVs
        (QuasiCoherentDescent.restrictForm C S hS rs pUs pVs hprs θ''))) :
    ψ ≫ derivationMove C S hS ZU ZH
        (@CategoryStruct.comp (AlgebraicSpaces C S hS) _ _ _ _ pU α) q hZU c hc θ (φ ≫ pX') hcq =
      derivationMove C S hS ZV ZH
        (@CategoryStruct.comp (AlgebraicSpaces C S hS) _ _ _ _ pV α) q hZV (ψ ≫ c) hc₂ θ₂
        (φ₂ ≫ pX') hcq₂ := by
  subst hZUs hZVs hZGs hZHs
  obtain rfl := eq_of_heq hαs
  obtain rfl := eq_of_heq hΩs
  obtain rfl := eq_of_heq hCs
  obtain rfl := eq_of_heq hpUs
  obtain rfl := eq_of_heq hpVs
  obtain rfl := eq_of_heq hrs
  obtain rfl := eq_of_heq hNU
  obtain rfl := eq_of_heq hNV
  obtain rfl := eq_of_heq heUs
  obtain rfl := eq_of_heq heVs
  exact comp_derivationMove_restriction_of_eq C S hS Z ZH ZU ZV ψ φ φ₂ hφ pUs pVs hsqU hsqV αs q
    pX' hZU hZV hW rs hr hprs eUs heU eVs heV c hc hcq hc₂ hcq₂ θ'' θ (eq_of_heq hθ) θ₂
    (eq_of_heq hθ₂)


section Sheaf

variable {X' Y' T : AlgebraicSpaces C S hS} {G : Subfunctor X'.obj} {H : Subfunctor Y'.obj}
  {hG : IsThickening C S hS X' G} {hH : IsThickening C S hS Y' H}
  (pX' : X' ⟶ T) (pY' : Y' ⟶ T)
  (a : IsThickening.space C S hS hG ⟶ IsThickening.space C S hS hH)
  (A : (modulePullback C S hS a).obj (conormalModule C S hS Y' ⟨H, hH.1⟩) ⟶
    conormalModule C S hS X' ⟨G, hG.1⟩)
  (hG₁ : IsFirstOrderThickening C S hS X' G) (hH₁ : IsFirstOrderThickening C S hS Y' H)

/-- **The action on the sheaf of lifts commutes with restriction.**  For a morphism
`k : V' ⟶ U'` of the spaces-étale site of `X'`, a section `θ` of the acting sheaf
`SheafHom_{𝒪_X}(a^*Ω_{Y/T}, 𝒞_{X/X'})` over `U'` — an `𝒪_U`-linear map
`(a^*Ω_{Y/T})|_U ⟶ 𝒞_{X/X'}|_U` — and a section `a'` of the sheaf of lifts of
[Stacks Project, Tag 061B] over `U'`: `(θ · a')|_{V'} = θ|_{V'} · a'|_{V'}`.  Here `θ` acts
through its reading `a|_U^*Ω_{Y/T} ⟶ 𝒞_{U/U'}` (Stacks 03LU and [Stacks Project, Tag 04CQ]), and
`θ|_{V'}` is the restriction of `θ` along `V ⟶ U`, read through Stacks 03LU. -/
@[stacks 061C "the action is an action of sheaves: it commutes with the restriction maps of the \
sheaf SheafHom_{O_X}(a^*Ω_{Y/B}, C_{X/X'}) and of the sheaf 061B"]
theorem conormalLiftAction_map {U' V' : SpacesEtale C S hS X'} (k : V' ⟶ U')
    (θ : (modulePullback C S hS
          (preimageProjection C S hS ((SpacesEtale.inclusion C S hS X').obj U').hom ⟨G, hG.1⟩)).obj
          ((modulePullback C S hS (Y := (⟨(⟨H, hH.1⟩ : ClosedSubspaces C S hS Y'.1).1.toFunctor,
            (⟨H, hH.1⟩ : ClosedSubspaces C S hS Y'.1).2.1⟩ : AlgebraicSpaces C S hS)) (X :=
              (⟨(⟨G, hG.1⟩ : ClosedSubspaces C S hS X'.1).1.toFunctor,
                (⟨G, hG.1⟩ : ClosedSubspaces C S hS X'.1).2.1⟩ : AlgebraicSpaces C S hS)) a).obj
            (sheafOfDifferentials C S hS (subspaceInclusion C S hS Y' ⟨H, hH.1⟩ ≫ pY'))) ⟶
        (modulePullback C S hS
          (preimageProjection C S hS ((SpacesEtale.inclusion C S hS X').obj U').hom ⟨G, hG.1⟩)).obj
          (conormalModule C S hS X' ⟨G, hG.1⟩))
    (s : (conormalLiftSubfunctor C S hS hG hH pX' pY' a A).obj (op U')) :
    (conormalLiftSubfunctor C S hS hG hH pX' pY' a A).toFunctor.map k.op
        (conormalLiftAction C S hS pX' pY' a A hG₁ hH₁ U' (Iso.homCongr
          ((modulePullbackCompIso C S hS (Z :=
            (⟨(⟨H, hH.1⟩ : ClosedSubspaces C S hS Y'.1).1.toFunctor,
              (⟨H, hH.1⟩ : ClosedSubspaces C S hS Y'.1).2.1⟩ : AlgebraicSpaces C S hS))
          (preimageProjection C S hS ((SpacesEtale.inclusion C S hS X').obj U').hom ⟨G, hG.1⟩)
            a).app (sheafOfDifferentials C S hS (subspaceInclusion C S hS Y' ⟨H, hH.1⟩ ≫ pY')))
          (conormalRestrictionIso C S hS hG U') θ) s) =
      conormalLiftAction C S hS pX' pY' a A hG₁ hH₁ V'
        (Iso.homCongr ((modulePullbackCompIso C S hS (Z :=
          (⟨(⟨H, hH.1⟩ : ClosedSubspaces C S hS Y'.1).1.toFunctor,
            (⟨H, hH.1⟩ : ClosedSubspaces C S hS Y'.1).2.1⟩ : AlgebraicSpaces C S hS))
          (preimageProjection C S hS ((SpacesEtale.inclusion C S hS X').obj V').hom ⟨G, hG.1⟩)
            a).app (sheafOfDifferentials C S hS (subspaceInclusion C S hS Y' ⟨H, hH.1⟩ ≫ pY')))
          (conormalRestrictionIso C S hS hG V')
          (QuasiCoherentDescent.restrictForm C S hS
            (P := (⟨((⟨G, hG.1⟩ : ClosedSubspaces C S hS X'.1).1.preimage
              ((SpacesEtale.inclusion C S hS X').obj V').hom.hom).toFunctor,
              (isClosedSubspace_preimage C S hS ((SpacesEtale.inclusion C S hS X').obj V').hom.hom
                (⟨G, hG.1⟩ : ClosedSubspaces C S hS X'.1).1 X'.2
                  ((SpacesEtale.inclusion C S hS X').obj V').left.2
                    (⟨G, hG.1⟩ : ClosedSubspaces C S hS X'.1).2).1⟩ :
              AlgebraicSpaces C S hS))
            (Q := (⟨((⟨G, hG.1⟩ : ClosedSubspaces C S hS X'.1).1.preimage
              ((SpacesEtale.inclusion C S hS X').obj U').hom.hom).toFunctor,
              (isClosedSubspace_preimage C S hS ((SpacesEtale.inclusion C S hS X').obj U').hom.hom
                (⟨G, hG.1⟩ : ClosedSubspaces C S hS X'.1).1 X'.2
                  ((SpacesEtale.inclusion C S hS X').obj U').left.2
                    (⟨G, hG.1⟩ : ClosedSubspaces C S hS X'.1).2).1⟩ :
              AlgebraicSpaces C S hS))
            ((SpacesEtale.toSpaces C S hS (IsThickening.space C S hS hG)).map
              ((thickeningPreimage C S hS hG).map k))
            (preimageProjection C S hS ((SpacesEtale.inclusion C S hS X').obj U').hom ⟨G, hG.1⟩)
            (preimageProjection C S hS ((SpacesEtale.inclusion C S hS X').obj V').hom ⟨G, hG.1⟩)
            (SpacesEtale.toSpaces_map_comp_structure C S hS (IsThickening.space C S hS hG)
              ((thickeningPreimage C S hS hG).map k)) θ))
        ((conormalLiftSubfunctor C S hS hG hH pX' pY' a A).toFunctor.map k.op s) := by
  have hU : ∀ W' : SpacesEtale C S hS X', (conormalRestrictionIso C S hS hG W').hom =
      conormalMap C S hS
        (preimageSubspace C S hS ((SpacesEtale.inclusion C S hS X').obj W').hom ⟨G, hG.1⟩)
        ⟨G, hG.1⟩ ((SpacesEtale.inclusion C S hS X').obj W').hom
        (preimageProjection C S hS ((SpacesEtale.inclusion C S hS X').obj W').hom ⟨G, hG.1⟩)
        (conormalEtaleRestrictionSquare C S hS ((SpacesEtale.inclusion C S hS X').obj W').hom
          ⟨G, hG.1⟩) := fun W' ↦
    @asIso_hom _ _ _ _ (conormalRestrictionMap C S hS hG W')
      (isIso_conormalMap_of_isEtale C S hS _ W'.property ⟨G, hG.1⟩)
  exact Subtype.ext (comp_derivationMove_restriction_of_spaces C S hS ⟨G, hG.1⟩ ⟨H, hH.1⟩
    (preimageSubspace C S hS ((SpacesEtale.inclusion C S hS X').obj U').hom ⟨G, hG.1⟩)
    (preimageSubspace C S hS ((SpacesEtale.inclusion C S hS X').obj V').hom ⟨G, hG.1⟩)
    ((SpacesEtale.toSpaces C S hS X').map k) ((SpacesEtale.inclusion C S hS X').obj U').hom
    ((SpacesEtale.inclusion C S hS X').obj V').hom
    (SpacesEtale.toSpaces_map_comp_structure C S hS X' k)
    (preimageProjection C S hS ((SpacesEtale.inclusion C S hS X').obj U').hom ⟨G, hG.1⟩)
    (preimageProjection C S hS ((SpacesEtale.inclusion C S hS X').obj V').hom ⟨G, hG.1⟩)
    (conormalEtaleRestrictionSquare C S hS ((SpacesEtale.inclusion C S hS X').obj U').hom
      ⟨G, hG.1⟩)
    (conormalEtaleRestrictionSquare C S hS ((SpacesEtale.inclusion C S hS X').obj V').hom
      ⟨G, hG.1⟩)
    a pY' pX'
    (isFirstOrderThickening_preimage C S hS G _ hG₁)
    (isFirstOrderThickening_preimage C S hS G _ hG₁) hH₁
    ((SpacesEtale.toSpaces C S hS (IsThickening.space C S hS hG)).map
      ((thickeningPreimage C S hS hG).map k))
    (toSpaces_map_thickeningPreimage_map_comp_subspaceInclusion C S hS hG k).symm
    (SpacesEtale.toSpaces_map_comp_structure C S hS (IsThickening.space C S hS hG)
      ((thickeningPreimage C S hS hG).map k))
    (conormalRestrictionIso C S hS hG U') (hU U') (conormalRestrictionIso C S hS hG V') (hU V')
    s.1 s.2.2.square s.2.1.1
    ((conormalLiftSubfunctor C S hS hG hH pX' pY' a A).toFunctor.map k.op s).2.2.square
    ((conormalLiftSubfunctor C S hS hG hH pX' pY' a A).toFunctor.map k.op s).2.1.1
    _ _ _ _
    (⟨(⟨G, hG.1⟩ : ClosedSubspaces C S hS X'.1).1.toFunctor,
      (⟨G, hG.1⟩ : ClosedSubspaces C S hS X'.1).2.1⟩ : AlgebraicSpaces C S hS)
    (⟨(⟨H, hH.1⟩ : ClosedSubspaces C S hS Y'.1).1.toFunctor,
      (⟨H, hH.1⟩ : ClosedSubspaces C S hS Y'.1).2.1⟩ : AlgebraicSpaces C S hS) (by rfl) (by rfl)
        (by rfl) (by rfl) a HEq.rfl _ HEq.rfl _ HEq.rfl
    (preimageProjection C S hS ((SpacesEtale.inclusion C S hS X').obj U').hom ⟨G, hG.1⟩) HEq.rfl
    (preimageProjection C S hS ((SpacesEtale.inclusion C S hS X').obj V').hom ⟨G, hG.1⟩) HEq.rfl
    ((SpacesEtale.toSpaces C S hS (IsThickening.space C S hS hG)).map
      ((thickeningPreimage C S hS hG).map k)) HEq.rfl
    (SpacesEtale.toSpaces_map_comp_structure C S hS (IsThickening.space C S hS hG)
      ((thickeningPreimage C S hS hG).map k))
    _ HEq.rfl _ HEq.rfl (conormalRestrictionIso C S hS hG U') HEq.rfl
    (conormalRestrictionIso C S hS hG V') HEq.rfl θ HEq.rfl HEq.rfl)

end Sheaf

end AlgebraicGeometry.Space

end
