module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedPushforwardInduction
public import StacksFrontier.Homology.DerivedCategory.MapHomologyIso

/-!
# A uniform upper bound for the cohomology of a quasi-compact quasi-separated algebraic space

Let `X` be a quasi-compact and quasi-separated algebraic space over a scheme `S` and let `RΓ` be
a right derived functor of the global sections `Γ(X, −) : Mod(𝒪_X) ⥤ Ab`. There is one integer
`N` such that `RΓ` carries every object of `D_QCoh(𝒪_X)` living in degrees `≤ c` to an object
living in degrees `≤ c + N`, for every `c`.

This is the finiteness of the cohomological dimension of `X` for quasi-coherent modules that
the proof of [Stacks, Tag 0CTM] uses to bound `RΓ(X, E ⊗^L 𝒪_X ⊗_R M)` uniformly in the module
`M`. The proof is the induction principle of [Stacks, Tag 08GP] run along the relative
Mayer–Vietoris triangles of [Stacks, Tag 08JK]: on an affine `Y` étale over `X` the higher
cohomology of a quasi-coherent module vanishes ([Stacks, Tag 03DW]), so the bound holds there
with `N = 0` by [Stacks, Tag 08F7]; and for an elementary distinguished square `(U, V)` of `W`,
the triangle `RΓ(W, E) → RΓ(U, E) ⊕ RΓ(V, E) → RΓ(U ×_W V, E) →` raises the bound by at most
one.

## Main results

* `AlgebraicGeometry.Space.isLE_obj_derivedPushforward_of_square`: the bound across one
  elementary distinguished square.
* `AlgebraicGeometry.Space.exists_isLE_derivedPushforward_of_affine`: the induction.
* `AlgebraicGeometry.Space.exists_isLE_rightDerived_baseRingGlobalSections`: the uniform bound
  for `RΓ(X, −)` on `D_QCoh(𝒪_X)`.

## References

* [Stacks Project, Tag 08GP](https://stacks.math.columbia.edu/tag/08GP)
* [Stacks Project, Tag 08JK](https://stacks.math.columbia.edu/tag/08JK)
* [Stacks Project, Tag 08F7](https://stacks.math.columbia.edu/tag/08F7)
* [Stacks Project, Tag 0CTM](https://stacks.math.columbia.edu/tag/0CTM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
  CategoryTheory.Pretriangulated

universe u v w

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

/-- **In a distinguished triangle the first object is one degree above the other two.** If
`T.obj₂` and `T.obj₃` live in degrees `≤ n`, then `T.obj₁` lives in degrees `≤ n + 1`: it is
an extension of `T.obj₂` by `T.obj₃⟦-1⟧`. -/
theorem isLE_obj₁_of_distTriang {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
    (T : Triangle (DerivedCategory C)) (hT : T ∈ distTriang (DerivedCategory C)) (n : ℤ)
    (h₂ : T.obj₂.IsLE n) (h₃ : T.obj₃.IsLE n) : T.obj₁.IsLE (n + 1) := by
  have h₁' : (T.obj₃⟦(-1 : ℤ)⟧).IsLE (n + 1) :=
    DerivedCategory.TStructure.t.isLE_shift T.obj₃ n (-1) (n + 1)
  have h₂' : T.obj₂.IsLE (n + 1) := DerivedCategory.TStructure.t.isLE_of_le T.obj₂ n (n + 1)
  exact DerivedCategory.TStructure.t.isLE₂ _ (inv_rot_of_distTriang T hT) (n + 1) h₁' h₂'

/-- **A triangulated functor keeps a biproduct of two objects in degrees `≤ n`** when it keeps
both summands there. -/
theorem isLE_obj_biprod {C D : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
    [Category* D] [Abelian D] [HasDerivedCategory D]
    (G : DerivedCategory C ⥤ DerivedCategory D) [G.CommShift ℤ] [G.IsTriangulated]
    (A A' : DerivedCategory C) (n : ℤ) (hA : (G.obj A).IsLE n) (hA' : (G.obj A').IsLE n) :
    (G.obj (A ⊞ A')).IsLE n :=
  DerivedCategory.TStructure.t.isLE₂ _
    (G.map_distinguished _ (binaryBiproductTriangle_distinguished A A')) n hA hA'

/-- **An exact functor keeps an object in degrees `≤ c`.** -/
theorem isLE_mapDerivedCategory_obj_of_exact {C D : Type*} [Category* C] [Abelian C]
    [HasDerivedCategory C] [Category* D] [Abelian D] [HasDerivedCategory D] (F : C ⥤ D)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (E : DerivedCategory C) (c : ℤ) (hE : E.IsLE c) : (F.mapDerivedCategory.obj E).IsLE c := by
  rw [DerivedCategory.isLE_iff] at hE ⊢
  intro i hi
  exact (F.map_isZero (hE i hi)).of_iso
    ((StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso F i).app E)

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Square

/-- **The relative Mayer–Vietoris triangle raises an upper bound by at most one.** Let
`(U ⊆ W, V ⟶ W)` be an elementary distinguished square with intersection `P`, let `w : W ⟶ Z`,
let `Rw`, `Ra`, `Rb`, `Rc` be right derived functors of the direct images along `w` and along
its restrictions to `U`, `V` and `P`, and let `G` be a triangulated functor out of `D(𝒪_Z)`. If
`G` carries `Ra(E|_U)`, `Rb(E|_V)` and `Rc(E|_P)` into degrees `≤ n`, it carries `Rw E` into
degrees `≤ n + 1`: the four objects sit in the distinguished triangle of Stacks 08JK. -/
theorem isLE_obj_derivedPushforward_of_square {W : AlgebraicSpaces B S hS}
    {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
    (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV) {Z : AlgebraicSpaces B S hS}
    (w : W ⟶ Z) {D : Type v} [Category.{w} D] [Abelian D] [HasDerivedCategory D]
    (G : DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2) ⥤ DerivedCategory D)
    [G.CommShift ℤ] [G.IsTriangulated]
    (Rw : DerivedCategory (Modules.{u, u} B S hS W.1 W.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2))
    (αw : (modulePushforward B S hS w).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rw)
    [Rw.IsRightDerivedFunctor αw
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ))]
    (Ra : DerivedCategory (Modules.{u, u} B S hS (edsOpen B S hS hsq).1 (edsOpen B S hS hsq).2) ⥤
      DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2))
    (αa : (modulePushforward B S hS (edsOpenHom B S hS hsq ≫ w)).mapHomotopyCategory
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Ra)
    [Ra.IsRightDerivedFunctor αa (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]
    (Rb : DerivedCategory
        (Modules.{u, u} B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2) ⥤
      DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2))
    (αb : (modulePushforward B S hS (edsEtaleHom B S hS hsq ≫ w)).mapHomotopyCategory
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rb)
    [Rb.IsRightDerivedFunctor αb (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]
    (Rc : DerivedCategory
        (Modules.{u, u} B S hS (edsInter B S hS hsq).1 (edsInter B S hS hsq).2) ⥤
      DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2))
    (αc : (modulePushforward B S hS (edsInterHom B S hS hsq ≫ w)).mapHomotopyCategory
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rc)
    [Rc.IsRightDerivedFunctor αc (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]
    (E : DerivedCategory (Modules.{u, u} B S hS W.1 W.2)) (n : ℤ)
    (hA : (G.obj (Ra.obj ((etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
      (isEtale_edsOpenHom B S hS hsq)).mapDerivedCategory.obj E))).IsLE n)
    (hB : (G.obj (Rb.obj ((etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory.obj E))).IsLE n)
    (hC : (G.obj (Rc.obj ((etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
      (isEtale_edsInterHom B S hS hsq)).mapDerivedCategory.obj E))).IsLE n) :
    (G.obj (Rw.obj E)).IsLE (n + 1) := by
  have hU := isRightDerivedFunctor_restrictPushDerivedUnit B S hS (edsOpenHom B S hS hsq)
    (isEtale_edsOpenHom B S hS hsq) (edsOpenHom B S hS hsq ≫ w) Ra αa
  have hV := isRightDerivedFunctor_restrictPushDerivedUnit B S hS (edsEtaleHom B S hS hsq)
    (isEtale_edsEtaleHom B S hS hsq) (edsEtaleHom B S hS hsq ≫ w) Rb αb
  have hP := isRightDerivedFunctor_restrictPushDerivedUnit B S hS (edsInterHom B S hS hsq)
    (isEtale_edsInterHom B S hS hsq) (edsInterHom B S hS hsq ≫ w) Rc αc
  obtain ⟨fU, fV', gU, gV, δ, hT⟩ :=
    exists_mem_distTriang_edsRelativeMayerVietoris_unconditional B S hS hsq w Rw _ _ _ αw
      (restrictPushDerivedUnit B S hS (edsOpenHom B S hS hsq) (isEtale_edsOpenHom B S hS hsq)
        (edsOpenHom B S hS hsq ≫ w) Ra αa)
      (restrictPushDerivedUnit B S hS (edsEtaleHom B S hS hsq) (isEtale_edsEtaleHom B S hS hsq)
        (edsEtaleHom B S hS hsq ≫ w) Rb αb)
      (restrictPushDerivedUnit B S hS (edsInterHom B S hS hsq) (isEtale_edsInterHom B S hS hsq)
        (edsInterHom B S hS hsq ≫ w) Rc αc)
      inferInstance hU hV hP E
  exact isLE_obj₁_of_distTriang _ (G.map_distinguished _ hT) n
    (isLE_obj_biprod G _ _ n hA hB) hC

end Square

section Induction

/-- **Induction on quasi-compact quasi-separated étale objects for upper bounds of derived direct
images.** Let `x : X ⟶ Z` with `X` quasi-compact and quasi-separated, `G` a triangulated functor
out of `D(𝒪_Z)`, and `𝓔_Y ⊆ D(𝒪_Y)` classes of objects stable under étale restriction. Suppose
that for every affine `Y` étale over `X` along `y`, every right derived functor `R` of
`(y ≫ x)_*` and every `E` in `𝓔_Y` living in degrees `≤ c`, the object `G(R E)` lives in degrees
`≤ c`. Then there is one integer `N` such that for every right derived functor `R` of `x_*` and
every `E` in `𝓔_X` living in degrees `≤ c`, the object `G(R E)` lives in degrees `≤ c + N`.
This is the induction principle of Stacks 08GP run with the relative Mayer–Vietoris triangle of
Stacks 08JK (`AlgebraicGeometry.Space.isLE_obj_derivedPushforward_of_square`). -/
theorem exists_isLE_derivedPushforward_of_affine (hZ : B.Contains (⊤_ Scheme.{u}))
    {X Z : AlgebraicSpaces B S hS} (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1) (x : X ⟶ Z)
    {D : Type v} [Category.{w} D] [Abelian D] [HasDerivedCategory D]
    (G : DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2) ⥤ DerivedCategory D)
    [G.CommShift ℤ] [G.IsTriangulated]
    (𝓔 : ∀ Y : AlgebraicSpaces B S hS,
      ObjectProperty (DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2)))
    (h𝓔 : ∀ {Y Y' : AlgebraicSpaces B S hS} (e : Y' ⟶ Y) (he : IsEtale B S hS e.hom) E,
      𝓔 Y E → 𝓔 Y' ((etaleModulePullback.{u, u} B S hS e he).mapDerivedCategory.obj E))
    (haff : ∀ (Y : AlgebraicSpaces B S hS) (y : Y ⟶ X), IsEtale B S hS y.hom →
      IsAffineSpace B S hS Y.1 → ∀ E, 𝓔 Y E → ∀ c : ℤ, E.IsLE c →
      ∀ (R : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2) ⥤
          DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2))
        (α : (modulePushforward B S hS (y ≫ x)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ R),
        R.IsRightDerivedFunctor α
          (HomotopyCategory.quasiIso (Modules.{u, u} B S hS Y.1 Y.2) (ComplexShape.up ℤ)) →
        (G.obj (R.obj E)).IsLE c) :
    ∃ N : ℤ, ∀ E, 𝓔 X E → ∀ c : ℤ, E.IsLE c →
      ∀ (R : DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤
          DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2))
        (α : (modulePushforward B S hS x).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ R),
        R.IsRightDerivedFunctor α
          (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ)) →
        (G.obj (R.obj E)).IsLE (c + N) := by
  let Ψ : (Y : AlgebraicSpaces B S hS) → (Y ⟶ Z) → ℤ → Prop := fun Y m N =>
    ∀ E, 𝓔 Y E → ∀ c : ℤ, E.IsLE c →
      ∀ (R : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2) ⥤
          DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2))
        (α : (modulePushforward B S hS m).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ R),
        R.IsRightDerivedFunctor α
          (HomotopyCategory.quasiIso (Modules.{u, u} B S hS Y.1 Y.2) (ComplexShape.up ℤ)) →
        (G.obj (R.obj E)).IsLE (c + N)
  let Φ : (Y : AlgebraicSpaces B S hS) → (Y ⟶ Z) → Prop := fun Y m => ∃ N : ℤ, Ψ Y m N
  have hcongr : ∀ {Y : AlgebraicSpaces B S hS} {m m' : Y ⟶ Z}, m = m' → Φ Y m → Φ Y m' := by
    rintro _ _ _ rfl h; exact h
  have key := qcqs_induction_on_self B S hS hZ X hXqc hXqs
    (fun Yp φ => ∀ hY : IsAlgebraicSpace B S hS Yp, IsEtale B S hS φ →
      Φ ⟨Yp, hY⟩ (ObjectProperty.homMk φ ≫ x))
    (fun V hV hY hφ => ⟨0, fun E hE c hc R α hR => by
      rw [add_zero]
      exact haff ⟨V.1.left.1, hY⟩ (ObjectProperty.homMk V.1.hom.hom) hφ hV E hE c hc R α hR⟩)
    (by
      intro W V U f hcomm hsq _ _ _ _ hU hV hInter hY hφ
      let W' : AlgebraicSpaces B S hS := ⟨W.1.left.1, hY⟩
      have hsq' : IsElementaryDistinguishedSquare B S hS W'.2 U f := hsq
      let w : W' ⟶ Z := ObjectProperty.homMk W.1.hom.hom ≫ x
      have hUΦ : Φ (edsOpen B S hS hsq') (edsOpenHom B S hS hsq' ≫ w) :=
        hcongr ((congrArg (· ≫ x) (ObjectProperty.hom_ext _ rfl)).trans (Category.assoc _ _ _))
          (hU hsq'.isOpenSubspace.1 (isEtale_comp B S hS (isEtale_edsOpenHom B S hS hsq') W.2))
      have hVΦ : Φ (edsEtale B S hS hsq') (edsEtaleHom B S hS hsq' ≫ w) :=
        hcongr ((congrArg (· ≫ x) (ObjectProperty.hom_ext _ hcomm.symm)).trans
            (Category.assoc _ _ _))
          (hV hsq'.isAlgebraicSpace V.2)
      have hPΦ : Φ (edsInter B S hS hsq') (edsInterHom B S hS hsq' ≫ w) :=
        hcongr ((congrArg (· ≫ x) (ObjectProperty.hom_ext _ (Category.assoc _ _ _).symm)).trans
            (Category.assoc _ _ _))
          (hInter (edsInter B S hS hsq').2 (by
            simpa only [Category.assoc] using
              isEtale_comp B S hS (f := pullback.fst U.ι f ≫ U.ι)
                (isEtale_edsInterHom B S hS hsq') W.2))
      obtain ⟨Na, hNa⟩ := hUΦ
      obtain ⟨Nb, hNb⟩ := hVΦ
      obtain ⟨Nc, hNc⟩ := hPΦ
      refine ⟨max Na (max Nb Nc) + 1, fun E hE c hc R α hR => ?_⟩
      have hside : ∀ (Y' : AlgebraicSpaces B S hS) (e : Y' ⟶ W') (he : IsEtale B S hS e.hom)
          (N : ℤ), N ≤ max Na (max Nb Nc) → Ψ Y' (e ≫ w) N →
          ∃ (R' : DerivedCategory (Modules.{u, u} B S hS Y'.1 Y'.2) ⥤
              DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2))
            (α' : (modulePushforward B S hS (e ≫ w)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
              DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ R')
            (_ : R'.IsRightDerivedFunctor α'
              (HomotopyCategory.quasiIso (Modules.{u, u} B S hS Y'.1 Y'.2) (ComplexShape.up ℤ))),
            (G.obj (R'.obj ((etaleModulePullback.{u, u} B S hS e he).mapDerivedCategory.obj
              E))).IsLE (c + max Na (max Nb Nc)) := by
        intro Y' e he N hN hΨ
        have := hasRightDerivedFunctor_mapMayerVietorisFunctor_modules B S hS
          (X := Y') (Z := Z) (modulePushforward B S hS (e ≫ w))
        let F := (modulePushforward B S hS (e ≫ w)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh
        let R' := F.totalRightDerived DerivedCategory.Qh
          (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
        let α' := F.totalRightDerivedUnit DerivedCategory.Qh
          (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
        have := hΨ _ (h𝓔 e he E hE) c (isLE_mapDerivedCategory_obj_of_exact _ E c hc) R' α'
          inferInstance
        refine ⟨R', α', inferInstance, ?_⟩
        exact DerivedCategory.TStructure.t.isLE_of_le _ (c + N) _ (by omega)
      obtain ⟨Ra, αa, _, hA⟩ := hside _ _ (isEtale_edsOpenHom B S hS hsq') Na (by omega) hNa
      obtain ⟨Rb, αb, _, hB⟩ := hside _ _ (isEtale_edsEtaleHom B S hS hsq') Nb (by omega) hNb
      obtain ⟨Rc, αc, _, hC⟩ := hside _ _ (isEtale_edsInterHom B S hS hsq') Nc (by omega) hNc
      have h := isLE_obj_derivedPushforward_of_square B S hS hsq' w G R α Ra αa Rb αb Rc αc E
        (c + max Na (max Nb Nc)) hA hB hC
      rwa [← add_assoc])
  exact hcongr (ObjectProperty.hom_ext _ (Category.id_comp _)) (key X.2 (isEtale_id B S hS X.1))

end Induction

end AlgebraicGeometry.Space

end
