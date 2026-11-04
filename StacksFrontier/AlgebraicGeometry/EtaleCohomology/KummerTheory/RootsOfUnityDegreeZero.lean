module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.PullbackComposition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RestrictionDegreeZero
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# `H⁰(X, μ_n)` and pullback in degree zero

A class of `H⁰(X_étale, μ_n)` is a global section of `μ_n`, that is an `n`-th root of unity in
`Γ(X, 𝒪_X)`. Under this identification the pullback `π^* : H⁰(Y, μ_n) ⟶ H⁰(X, μ_n)` along a
morphism of schemes `π : X ⟶ Y` is `Units.map π^#`. Consequently, for `X` integral over a field
`K` containing `n` distinct `n`-th roots of unity, `H⁰(X, μ_n) ≅ ℤ/n` and every endomorphism of
`X` over `K` acts trivially on `H⁰(X, μ_n)`: all `n`-th roots of unity of `Γ(X, 𝒪_X)` come from
`K`.

## Main results

* `Stacks.EtaleCohomology.h0RootsOfUnityAddEquiv`: `H⁰(X, μ_n) ≃+ μ_n(Γ(X, 𝒪_X))`.
* `Stacks.EtaleCohomology.h0RootsOfUnityAddEquiv_rootsOfUnityPullbackMap`: pullback is
  `Units.map π^#`.
* `Stacks.EtaleCohomology.rootsOfUnityPullbackMap_zero_eq_self`: an endomorphism over the field
  acts trivially on `H⁰`.
* `Stacks.EtaleCohomology.h0RootsOfUnityAddEquivZMod`: `H⁰(X, μ_n) ≃+ ℤ/n`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Stacks.Kummer

universe u v w

namespace Stacks.EtaleCohomology

section Sections

variable (X : Scheme.{u}) (n : ℕ)

/-- The root of unity underlying a section of `μ_n` is additive in the section. -/
theorem rootsOfUnitySection_add (U : X.Etaleᵒᵖ)
    (s t : ToType ((rootsOfUnitySheaf.{u, v} X n).obj.obj U)) :
    (rootsOfUnitySection.{u, v} X n U (s + t)).1 =
      (rootsOfUnitySection.{u, v} X n U s).1 * (rootsOfUnitySection.{u, v} X n U t).1 := by
  show Additive.toMul (((rootsOfUnityι.{u, v} X n).hom.app U (s + t)).down) = _
  rw [map_add]
  rfl

/-- **Global sections of `μ_n` are the `n`-th roots of unity of `Γ(X, 𝒪_X)`**, as groups. -/
def rootsOfUnityGlobalSectionsAddEquiv :
    ToType ((rootsOfUnitySheaf.{u, v} X n).obj.obj (op (Scheme.Etale.mk (𝟙 X)))) ≃+
      Additive (rootsOfUnity n Γ(X, ⊤)) where
  toFun s := Additive.ofMul ⟨(rootsOfUnitySection.{u, v} X n _ s).1,
    (rootsOfUnitySection.{u, v} X n _ s).2⟩
  invFun r := (rootsOfUnitySectionsEquiv.{u, v} X n _).symm ⟨r.toMul.1, r.toMul.2⟩
  left_inv s := by
    change (rootsOfUnitySectionsEquiv.{u, v} X n _).symm
      (rootsOfUnitySectionsEquiv.{u, v} X n _ s) = s
    exact Equiv.symm_apply_apply _ _
  right_inv r := Additive.toMul.injective <| Subtype.ext <| congrArg (fun z => z.1)
    (Equiv.apply_symm_apply (rootsOfUnitySectionsEquiv.{u, v} X n
      (op (Scheme.Etale.mk (𝟙 X)))) ⟨r.toMul.1, r.toMul.2⟩)
  map_add' s t :=
    Additive.toMul.injective (Subtype.ext (rootsOfUnitySection_add.{u, v} X n _ s t))

variable [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]

/-- **`H⁰(X_étale, μ_n) ≃+ μ_n(Γ(X, 𝒪_X))`.** -/
def h0RootsOfUnityAddEquiv :
    Sheaf.H.{w} (rootsOfUnitySheaf.{u, v} X n) 0 ≃+ Additive (rootsOfUnity n Γ(X, ⊤)) :=
  (Sheaf.H.equiv₀ _ (isTerminalEtaleMkId X)).trans (rootsOfUnityGlobalSectionsAddEquiv.{u, v} X n)

end Sections

section Pullback

variable {X Y : Scheme.{u}} (π : X ⟶ Y) (n : ℕ)
  [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]

omit [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})] in
/-- The global section of `μ_{n,X}` obtained from a global section of `μ_{n,Y}` by the unit of
`π^{-1} ⊣ π_*`, restriction to the final object and the comparison `π^{-1} μ_n ⟶ μ_n` is the
pulled back root of unity. -/
theorem rootsOfUnityι_comparison_unit (s : ToType ((rootsOfUnitySheaf.{u, v} Y n).obj.obj
      (op (Scheme.Etale.mk (𝟙 Y))))) :
    (rootsOfUnityι.{u, v} X n).hom.app (op (Scheme.Etale.mk (𝟙 X)))
        ((rootsOfUnityInverseImageComparison.{u, v} π n).hom.app (op (Scheme.Etale.mk (𝟙 X)))
          (((etaleAbelianInverseImage.{u, v} π).obj (rootsOfUnitySheaf.{u, v} Y n)).obj.map
            (((isTerminalEtaleMkId Y).isTerminalObj (smallEtaleBaseChange π)).from
              (Scheme.Etale.mk (𝟙 X))).op
            (((etaleAbelianInverseImageDirectImageAdj.{u, v} π).unit.app
              (rootsOfUnitySheaf.{u, v} Y n)).hom.app (op (Scheme.Etale.mk (𝟙 Y))) s))) =
      ofUnit (U := Scheme.Etale.mk (𝟙 X)) ((Units.map (π.appTop.hom : Γ(Y, ⊤) →* Γ(X, ⊤))
        ((rootsOfUnitySection.{u, v} Y n _ s).1 : Γ(Y, ⊤)ˣ) : Γ(X, ⊤)ˣ)) := by
  set b := ((isTerminalEtaleMkId Y).isTerminalObj (smallEtaleBaseChange π)).from
    (Scheme.Etale.mk (𝟙 X))
  set P := etaleAbelianInverseImage.{u, v} π
  set adj := etaleAbelianInverseImageDirectImageAdj.{u, v} π
  set w := ((adj.unit.app (rootsOfUnitySheaf.{u, v} Y n)).hom.app (op (Scheme.Etale.mk (𝟙 Y))) s)
  have h1 := ConcreteCategory.congr_hom
    (congrArg (fun f => f.hom.app (op (Scheme.Etale.mk (𝟙 X))))
      (rootsOfUnityInverseImageComparison_comp_rootsOfUnityι.{u, v} π n))
    ((P.obj (rootsOfUnitySheaf.{u, v} Y n)).obj.map b.op w)
  have h2 := ConcreteCategory.congr_hom
    ((P.map (rootsOfUnityι.{u, v} Y n)).hom.naturality b.op) w
  have h3 := ConcreteCategory.congr_hom
    ((multiplicativeInverseImageComparison.{u, v} π).hom.naturality b.op)
    ((P.map (rootsOfUnityι.{u, v} Y n)).hom.app _ w)
  have h4 := ConcreteCategory.congr_hom
    ((adj.unit.naturality (rootsOfUnityι.{u, v} Y n)).symm ▸ rfl :
      (adj.unit.app _ ≫ (etaleAbelianDirectImage.{u, v} π).map (P.map (rootsOfUnityι.{u, v} Y n))
        ).hom.app (op (Scheme.Etale.mk (𝟙 Y))) =
      (rootsOfUnityι.{u, v} Y n ≫ adj.unit.app _).hom.app (op (Scheme.Etale.mk (𝟙 Y)))) s
  have h5 := multiplicativeInverseImageComparison_app_ofUnit.{u, v} π (Scheme.Etale.mk (𝟙 Y))
    (rootsOfUnitySection.{u, v} Y n _ s).1
  have e4 : (P.map (rootsOfUnityι.{u, v} Y n)).hom.app
      (op ((smallEtaleBaseChange π).obj (Scheme.Etale.mk (𝟙 Y)))) w =
      (adj.unit.app (multiplicativeSheaf.{u, v} Y)).hom.app (op (Scheme.Etale.mk (𝟙 Y)))
        (ofUnit (rootsOfUnitySection.{u, v} Y n _ s).1) := by
    rw [← rootsOfUnityι_app_eq_ofUnit]
    exact h4
  have hb : b.left ≫ pullback.fst (Scheme.Etale.mk (𝟙 Y)).hom π = π := by
    have hw : b.left ≫ pullback.snd (Scheme.Etale.mk (𝟙 Y)).hom π = 𝟙 X := MorphismProperty.Over.w b
    have hc : pullback.fst (Scheme.Etale.mk (𝟙 Y)).hom π =
        pullback.snd (Scheme.Etale.mk (𝟙 Y)).hom π ≫ π :=
      (Category.comp_id _).symm.trans pullback.condition
    refine (congrArg (fun h => b.left ≫ h) hc).trans ?_
    show (b.left ≫ pullback.snd (Scheme.Etale.mk (𝟙 Y)).hom π) ≫ π = π
    rw [hw]
    exact Category.id_comp π
  refine h1.trans ?_
  refine (congrArg ((multiplicativeInverseImageComparison.{u, v} π).hom.app
    (op (Scheme.Etale.mk (𝟙 X)))) h2).trans ?_
  refine h3.trans ?_
  refine (congrArg (fun z => (multiplicativeSheaf.{u, v} X).obj.map b.op
    ((multiplicativeInverseImageComparison.{u, v} π).hom.app _ z)) e4).trans ?_
  refine (congrArg (fun z => (multiplicativeSheaf.{u, v} X).obj.map b.op z) h5).trans ?_
  refine (map_ofUnit.{u, v} b _).trans ?_
  congr 1
  ext
  show (b.left.appTop.hom ((pullback.fst (Scheme.Etale.mk (𝟙 Y)).hom π).appTop.hom _)) =
    π.appTop.hom _
  exact congrArg (fun f : X ⟶ Y => f.appTop.hom
    (Units.val (α := Γ(Y, ⊤)) (rootsOfUnitySection.{u, v} Y n _ s).1)) hb

/-- **Pullback on `H⁰(-, μ_n)` is `Units.map π^#` on roots of unity.** -/
theorem h0RootsOfUnityAddEquiv_rootsOfUnityPullbackMap
    (x : Sheaf.H.{w} (rootsOfUnitySheaf.{u, v} Y n) 0) :
    ((h0RootsOfUnityAddEquiv.{u, v, w} X n (rootsOfUnityPullbackMap.{u, v, w} π n 0 x)).toMul :
        Γ(X, ⊤)ˣ) =
      Units.map π.appTop.hom ((h0RootsOfUnityAddEquiv.{u, v, w} Y n x).toMul : Γ(Y, ⊤)ˣ) := by
  have hres := equiv₀_etaleCohomologyRestrictionMap_zero.{u, v, w} π
    (rootsOfUnitySheaf.{u, v} Y n) (isTerminalEtaleMkId X) x
  have key := rootsOfUnityι_comparison_unit.{u, v} π n (Sheaf.H.equiv₀ _ (isTerminalEtaleMkId Y) x)
  refine ofUnit_injective.{u, v} (X := X) (U := Scheme.Etale.mk (𝟙 X))
    ((rootsOfUnityι_app_eq_ofUnit.{u, v} X n _ _).symm.trans ((congrArg _ ?_).trans key))
  rw [rootsOfUnityPullbackMap_apply]
  erw [← Sheaf.H.equiv₀_naturality]
  rw [hres]

end Pullback

section OverField

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X] (g : X ⟶ Spec (.of K)) {n : ℕ}
  [NeZero n] {ζ : K} (hζ : IsPrimitiveRoot ζ n)

/-- The image in `Γ(X, 𝒪_X)ˣ` of a primitive `n`-th root of unity of the base field. -/
def globalPrimitiveRoot : Γ(X, ⊤)ˣ :=
  (((hζ.map_of_injective (f := ((Scheme.ΓSpecIso (.of K)).inv ≫ g.appTop).hom)
    (RingHom.injective _)).isUnit (NeZero.ne n))).unit

/-- The image of `ζ` in `Γ(X, 𝒪_X)ˣ` is a primitive `n`-th root of unity. -/
theorem isPrimitiveRoot_globalPrimitiveRoot : IsPrimitiveRoot (globalPrimitiveRoot g hζ) n :=
  IsPrimitiveRoot.coe_units_iff.mp
    (hζ.map_of_injective (f := ((Scheme.ΓSpecIso (.of K)).inv ≫ g.appTop).hom)
      (RingHom.injective _))

/-- The `n`-th roots of unity of `Γ(X, 𝒪_X)` are the powers of the image of `ζ`. -/
theorem rootsOfUnity_eq_zpowers_globalPrimitiveRoot :
    rootsOfUnity n Γ(X, ⊤) = Subgroup.zpowers (globalPrimitiveRoot g hζ) :=
  ((isPrimitiveRoot_globalPrimitiveRoot g hζ).zpowers_eq).symm

/-- An endomorphism `φ` of `X` over `K` fixes the image of `ζ`. -/
theorem units_map_globalPrimitiveRoot (φ : X ⟶ X) (w : φ ≫ g = g) :
    Units.map (φ.appTop.hom : Γ(X, ⊤) →* Γ(X, ⊤)) (globalPrimitiveRoot g hζ) =
      globalPrimitiveRoot g hζ := by
  ext
  show φ.appTop.hom (g.appTop.hom ((Scheme.ΓSpecIso (.of K)).inv.hom ζ)) =
    g.appTop.hom ((Scheme.ΓSpecIso (.of K)).inv.hom ζ)
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, w]

variable [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]

include hζ in
/-- **An endomorphism over the field acts trivially on `H⁰(X, μ_n)`** for `X` integral over a
field containing a primitive `n`-th root of unity: the global `n`-th roots of unity are the
powers of the image of a primitive root of the field. -/
theorem rootsOfUnityPullbackMap_zero_eq_self (φ : X ⟶ X) (w : φ ≫ g = g)
    (x : Sheaf.H.{w} (rootsOfUnitySheaf.{u, v} X n) 0) :
    rootsOfUnityPullbackMap.{u, v, w} φ n 0 x = x := by
  apply (h0RootsOfUnityAddEquiv.{u, v, w} X n).injective
  apply Additive.toMul.injective
  apply Subtype.ext
  rw [h0RootsOfUnityAddEquiv_rootsOfUnityPullbackMap]
  have hmem : ((h0RootsOfUnityAddEquiv.{u, v, w} X n x).toMul : Γ(X, ⊤)ˣ) ∈
      Subgroup.zpowers (globalPrimitiveRoot g hζ) := by
    rw [← rootsOfUnity_eq_zpowers_globalPrimitiveRoot g hζ]
    exact (h0RootsOfUnityAddEquiv.{u, v, w} X n x).toMul.2
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmem
  rw [← hm, map_zpow, units_map_globalPrimitiveRoot g hζ φ w]

/-- **`H⁰(X, μ_n) ≃+ ℤ/n`** for `X` integral over a field containing a primitive `n`-th root of
unity. -/
def h0RootsOfUnityAddEquivZMod :
    Sheaf.H.{w} (rootsOfUnitySheaf.{u, v} X n) 0 ≃+ ZMod n :=
  (h0RootsOfUnityAddEquiv.{u, v, w} X n).trans
    ((MulEquiv.subgroupCongr (rootsOfUnity_eq_zpowers_globalPrimitiveRoot g hζ)).toAdditive.trans
      ((isPrimitiveRoot_globalPrimitiveRoot g hζ).zmodEquivZPowers.symm))

end OverField

end Stacks.EtaleCohomology

end
