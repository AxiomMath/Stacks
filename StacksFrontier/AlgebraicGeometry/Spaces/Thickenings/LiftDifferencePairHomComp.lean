module

public import StacksFrontier.AlgebraicGeometry.Spaces.LiftDifferenceTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardCompIsoSheafTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ConormalMapComorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftDifferencePairHom
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftDifferenceRingSurjectivity
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.RestrictedSharpComp

/-!
# The difference of two morphisms of thickenings under precomposition

Let `(k₀, k) : (Z_U ⊆ U') ⟶ (Z_X ⊆ X')` be a morphism of first order thickenings and let
`(e₀, c), (e₀, c') : (Z_X ⊆ X') ⟶ (W₀ ⊆ W)` be two morphisms of pairs agreeing on `Z_X`.  The
difference of `c` and `c'` is a linear map `θ : e₀^*Ω_{W₀/B} ⟶ 𝒞_{Z_X/X'}`
([Stacks Project, Tag 0618] with Equation (0619)), and so is the difference of the precomposed
pair `k ≫ c, k ≫ c'`.  This file proves that the second is the restriction of the first along
`(k₀, k)`: read through the adjunctions `e^* ⊣ e_*` on the small étale site of `W₀`, the transpose
of the second is the transpose of the first followed by the map

`κ : (e₀)_*𝒞_{Z_X/X'} ⟶ (k₀ ≫ e₀)_*𝒞_{Z_U/U'}`

induced by the comorphism of `k`, and these maps are functorial in `(k₀, k)`.

## Main definitions

* `AlgebraicGeometry.Space.conormalInverseImageSquareZeroValues`: the conormal module of a first
  order thickening as a square-zero ideal of `i^{-1}𝒪_{X'}`.
* `AlgebraicGeometry.Space.conormalComorphism`: the map `𝒞_{Z_X/X'} ⟶ (k₀)_*𝒞_{Z_U/U'}` induced
  by the comorphism of `k` on the kernels of the two reductions.

## References

* [Stacks Project, Tag 0618](https://stacks.math.columbia.edu/tag/0618)
* [Stacks Project, Tag 0619](https://stacks.math.columbia.edu/tag/0619)
* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP), of which the map of
  conormal modules is the kernel-side reading.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Kernel

variable {X' U' : AlgebraicSpaces B S hS} (ZX : ClosedSubspaces B S hS X'.1)
  (ZU : ClosedSubspaces B S hS U'.1) (hZX : IsFirstOrderThickening B S hS X' ZX.1)
  (hZU : IsFirstOrderThickening B S hS U' ZU.1)

/-- **The conormal module of a first order thickening as a square-zero ideal of
`i^{-1}𝒪_{X'}`**, through the inclusion `AlgebraicGeometry.Space.conormalInverseImageι`. -/
def conormalInverseImageSquareZeroValues :
    Stacks.Sites.SquareZeroValues (conormalModule B S hS X' ZX) where
  ambient := structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X' ZX)
  ambient_mul_comm {V} s t :=
    haveI : PreservesFiniteProducts
        (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X' ZX)).inverseImage :=
      haveI :=
        (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X' ZX)).preservesFiniteLimits
      ⟨fun _ => inferInstance⟩
    pullback_sections_mul_comm (R := structureRingSheaf B S hS X')
      (SmallEtale.topology B S hS (⟨ZX.1.toFunctor, ZX.2.1⟩ : AlgebraicSpaces B S hS).1)
      (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X' ZX)).inverseImage
      (ringSheaf_mul_comm_smallEtaleRingedSite B S hS X') V s t
  ι {V} := ((conormalInverseImageι B S hS ZX hZX).val.app V).hom.toAddMonoidHom
  ι_injective {V} := conormalInverseImageι_injective B S hS ZX hZX V
  ι_map h m := conormalInverseImageι_val_app_map B S hS ZX hZX h m
  mul_ι_eq_zero {V} m m' := mul_app_conormalInverseImageι_eq_zero B S hS ZX hZX V m m'

/-- The inclusion of the ideal of values of
`AlgebraicGeometry.Space.conormalInverseImageSquareZeroValues` is
`AlgebraicGeometry.Space.conormalInverseImageι` on sections. -/
theorem conormalInverseImageSquareZeroValues_ι
    {V : (SmallEtale B S hS (⟨ZX.1.toFunctor, ZX.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ}
    (m : (conormalModule B S hS X' ZX).val.obj V) :
    (conormalInverseImageSquareZeroValues B S hS ZX hZX).ι m =
      (conormalInverseImageι B S hS ZX hZX).val.app V m := rfl

variable (k : U' ⟶ X')
  (k₀ : (⟨ZU.1.toFunctor, ZU.2.1⟩ : AlgebraicSpaces B S hS) ⟶
    (⟨ZX.1.toFunctor, ZX.2.1⟩ : AlgebraicSpaces B S hS))
  (hk : subspaceInclusion B S hS U' ZU ≫ k = k₀ ≫ subspaceInclusion B S hS X' ZX)

/-- The comorphism of `k`, read on the small étale site of `Z_X`, carries the kernel of the
reduction of `i_X^{-1}𝒪_{X'}` into the direct image of the kernel of the reduction of
`i_U^{-1}𝒪_{U'}`. -/
theorem exists_restrictedSquareZeroValues_ι_eq_restrictedSharp
    {V : (SmallEtale B S hS (⟨ZX.1.toFunctor, ZX.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ}
    (m : (conormalModule B S hS X' ZX).val.obj V) :
    ∃ m' : ((modulePushforward B S hS k₀).obj (conormalModule B S hS U' ZU)).val.obj V,
      (restrictedSquareZeroValues B S hS ZU ZX k₀ hZU).ι m' =
        (restrictedSharpThroughThickening B S hS ZU ZX k k₀ hk).hom.app V
          ((conormalInverseImageSquareZeroValues B S hS ZX hZX).ι m) := by
  have := preservesFiniteLimits_smallToposMorphismTypeU_pushforward B S hS k₀
  refine exists_app_pullbackModuleMap_eq
    (SmallEtale.topology B S hS (⟨ZX.1.toFunctor, ZX.2.1⟩ : AlgebraicSpaces B S hS).1)
    (smallToposMorphismTypeU B S hS k₀).pushforward
    (conormalInverseImageι B S hS ZU hZU)
    (structureSharpRingInverseImage B S hS (subspaceInclusion B S hS U' ZU)) V
    (app_conormalInverseImageι_eq_zero B S hS ZU hZU)
    (conormalInverseImageι_injective B S hS ZU hZU)
    (exists_conormalInverseImageι_eq B S hS ZU hZU) _ ?_
  have h := ConcreteCategory.congr_hom (congrArg (fun n => n.hom.app V)
    (restrictedSharpThroughThickening_comp_reduction_structureSharp B S hS ZU ZX k₀ k hk))
    ((conormalInverseImageSquareZeroValues B S hS ZX hZX).ι m)
  refine h.trans ?_
  show (structureSharp B S hS k₀).hom.app V ((structureSharpRingInverseImage B S hS
    (subspaceInclusion B S hS X' ZX)).hom.app V ((conormalInverseImageι B S hS ZX hZX).val.app V
      m)) = 0
  rw [app_conormalInverseImageι_eq_zero B S hS ZX hZX V m, map_zero]

/-- **The map of conormal modules induced by a morphism of first order thickenings**,
`𝒞_{Z_X/X'} ⟶ (k₀)_*𝒞_{Z_U/U'}`: the comorphism of `k` read on the small étale site of `Z_X`,
`AlgebraicGeometry.Space.restrictedSharpThroughThickening`, restricted to the kernels of the two
reductions.  It is the transpose of the canonical map `k₀^*𝒞_{Z_X/X'} ⟶ 𝒞_{Z_U/U'}` of
[Stacks Project, Tag 04CP], in its kernel-side reading. -/
def conormalComorphism :
    conormalModule B S hS X' ZX ⟶ (modulePushforward B S hS k₀).obj (conormalModule B S hS U' ZU) :=
  Stacks.Sites.SquareZeroValues.transport (q := structureSharpRingInverseImage B S hS
      (subspaceInclusion B S hS X' ZX))
    (hq := isLocallySurjective_structureSharpRingInverseImage B S hS
      (subspaceInclusion B S hS X' ZX) ZX.2.2)
    (conormalInverseImageSquareZeroValues B S hS ZX hZX)
    (restrictedSquareZeroValues B S hS ZU ZX k₀ hZU)
    (restrictedSharpThroughThickening B S hS ZU ZX k k₀ hk)
    (fun m => exists_restrictedSquareZeroValues_ι_eq_restrictedSharp B S hS ZX ZU hZX hZU k k₀ hk m)
    (𝟙 _) (fun x m => ((conormalInverseImageι B S hS ZX hZX).val.app _).hom.map_smul x m)
    (fun x m => restrictedSquareZeroValues_ι_smul B S hS ZU ZX k₀ hZU k hk x m)

/-- **The defining equation of the map of conormal modules**: on the kernels, it is the
comorphism of `k`. -/
theorem ι_conormalComorphism
    {V : (SmallEtale B S hS (⟨ZX.1.toFunctor, ZX.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ}
    (m : (conormalModule B S hS X' ZX).val.obj V) :
    (restrictedSquareZeroValues B S hS ZU ZX k₀ hZU).ι
        ((conormalComorphism B S hS ZX ZU hZX hZU k k₀ hk).val.app V m) =
      (restrictedSharpThroughThickening B S hS ZU ZX k k₀ hk).hom.app V
        ((conormalInverseImageι B S hS ZX hZX).val.app V m) :=
  Stacks.Sites.SquareZeroValues.ι_transportApp _ _ _
    (fun m => exists_restrictedSquareZeroValues_ι_eq_restrictedSharp B S hS ZX ZU hZX hZU k k₀ hk m)
    m

end Kernel


/-- The naturality of a transformation into a composite of functors of sheaves of sets, read
on a local section.  Stated with every object a variable. -/
theorem _root_.CategoryTheory.Sheaf.natTrans_comp_naturality_apply {C₁ C₂ C₃ : Type*}
    [Category C₁] [Category C₂] [Category C₃] {J₁ : GrothendieckTopology C₁}
    {J₂ : GrothendieckTopology C₂} {J₃ : GrothendieckTopology C₃}
    (F : Sheaf J₁ (Type u) ⥤ Sheaf J₂ (Type u)) (G : Sheaf J₂ (Type u) ⥤ Sheaf J₃ (Type u))
    (H : Sheaf J₁ (Type u) ⥤ Sheaf J₃ (Type u)) (θ : F ⋙ G ⟶ H) (X : Sheaf J₁ (Type u))
    {Y : Sheaf J₁ (Type u)} (φ : X ⟶ Y) (V : C₃ᵒᵖ) (z : ((F ⋙ G).obj X).obj.obj V) :
    (H.map φ).hom.app V ((θ.app X).hom.app V z) =
      (θ.app Y).hom.app V ((G.map (F.map φ)).hom.app V z) :=
  (congrFun (congrArg (fun t => t.hom.app V) (θ.naturality φ)) z).symm

/-- The geometric comparison of iterated direct images at the sheaf of sets underlying an
`𝒪_Z`-module and at the sheaf of sets underlying its restriction of scalars along
`i^♯ : i^{-1}𝒪_X ⟶ 𝒪_Z` agree on sections: the two sheaves of sets are the same. -/
theorem smallToposMorphismTypeU_comp_app_restrictScalars {X : AlgebraicSpaces B S hS}
    (Z : ClosedSubspaces B S hS X.1) {V₂ V₃ : AlgebraicSpaces B S hS}
    (f : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ V₂) (g : V₂ ⟶ V₃)
    (M : Modules.{u, u} B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1
      (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).2)
    (V : (SmallEtale B S hS V₃.1)ᵒᵖ)
    (z : (((smallToposMorphismTypeU B S hS f).pushforward ⋙
      (smallToposMorphismTypeU B S hS g).pushforward).obj
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS
          (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))).obj M)).obj.obj V) :
    ((smallToposMorphismTypeU_comp B S hS f g).hom.app
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS
          (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))).obj M)).hom.app V z =
      ((smallToposMorphismTypeU_comp B S hS f g).hom.app
        ((Sheaf.moduleSheafFunctor.{u, u, u + 1} (structureRingSheafInverseImage B S hS
          (subspaceInclusion B S hS X Z))).obj ((SheafOfModules.restrictScalars
          (structureSharpRingInverseImage B S hS
            (subspaceInclusion B S hS X Z))).obj M))).hom.app V z := rfl

/-- A functor of sheaves of sets carries an equality of composites to an equality of iterated
applications on a local section.  Stated with every object a variable. -/
theorem _root_.CategoryTheory.Sheaf.map_map_hom_app_eq {C₁ C₂ : Type*} [Category C₁]
    [Category C₂] {J₁ : GrothendieckTopology C₁} {J₂ : GrothendieckTopology C₂}
    (P : Sheaf J₁ (Type u) ⥤ Sheaf J₂ (Type u)) {A Bq Bq' Cq : Sheaf J₁ (Type u)}
    (a : A ⟶ Bq) (b : Bq ⟶ Cq) (a' : A ⟶ Bq') (b' : Bq' ⟶ Cq) (h : a ≫ b = a' ≫ b')
    (V : C₂ᵒᵖ) (x : (P.obj A).obj.obj V) :
    (P.map b).hom.app V ((P.map a).hom.app V x) = (P.map b').hom.app V ((P.map a').hom.app V x) :=
  congrFun (congrArg (fun t => t.hom.app V)
    ((P.map_comp a b).symm.trans ((congrArg P.map h).trans (P.map_comp a' b')))) x

/-- **The transpose of a morphism out of a composite of left adjoints**, read through the
uniqueness of left adjoints.  For adjunctions `F₁ ⊣ G₁`, `F₂ ⊣ G₂` and `F' ⊣ G'` with
`G₂ ⋙ G₁ ≅ G'`, the transpose along `F' ⊣ G'` of `F'X ≅ F₂F₁X ⟶ F₂Y ⟶ Z` built from
`θ : F₁X ⟶ Y` and the transpose of `κ : Y ⟶ G₂Z` is the transpose of `θ` followed by `G₁κ` and the
comparison. -/
theorem _root_.CategoryTheory.Adjunction.homEquiv_leftAdjointUniq_inv_comp {C D E : Type*}
    [Category C] [Category D] [Category E] {F₁ : C ⥤ D} {G₁ : D ⥤ C} {F₂ : D ⥤ E} {G₂ : E ⥤ D}
    {F' : C ⥤ E} {G' : E ⥤ C} (a₁ : F₁ ⊣ G₁) (a₂ : F₂ ⊣ G₂) (i : G₂ ⋙ G₁ ≅ G') (a' : F' ⊣ G')
    (a : F₁ ⋙ F₂ ⊣ G') (ha : a = (a₁.comp a₂).ofNatIsoRight i)
    {X : C} {Y : D} {Z : E} (θ : F₁.obj X ⟶ Y) (κ : Y ⟶ G₂.obj Z) :
    a'.homEquiv _ _ ((Adjunction.leftAdjointUniq a a').inv.app X ≫
        F₂.map θ ≫ (a₂.homEquiv _ _).symm κ) =
      a₁.homEquiv _ _ θ ≫ G₁.map κ ≫ i.hom.app Z := by
  subst ha
  rw [Adjunction.leftAdjointUniq_inv_app, Adjunction.homEquiv_unit, Functor.map_comp,
    ← Category.assoc, Adjunction.unit_leftAdjointUniq_hom_app, ← Adjunction.homEquiv_unit]
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv, Equiv.trans_apply,
    Adjunction.homEquiv_naturality_left, Equiv.apply_symm_apply,
    Adjunction.homEquiv_naturality_right, Category.assoc]

section Generic

variable {V₁ V₂ V₃ : AlgebraicSpaces B S hS} (f : V₁ ⟶ V₂) (g : V₂ ⟶ V₃)
  {N : Modules.{u, u} B S hS V₂.1 V₂.2} {N' : Modules.{u, u} B S hS V₁.1 V₁.2}
  (al : N ⟶ (modulePushforward B S hS f).obj N')

/-- The direct image along `g` of a morphism into a direct image along `f`, read as a morphism
into the direct image along `f ≫ g` through the comparison of [Stacks Project, Tag 03LU]. -/
abbrev modulePushforwardCompMap :
    (modulePushforward B S hS g).obj N ⟶ (modulePushforward B S hS (f ≫ g)).obj N' :=
  (modulePushforward B S hS g).map al ≫ (modulePushforwardCompIso B S hS f g).hom.app N'

/-- The direct image of modules acts on sections as the direct image of sheaves of sets of
[Stacks Project, Tag 03G2], part (3), on the underlying sheaves. -/
theorem modulePushforward_map_val_app_typeU {M M' : Modules.{u, u} B S hS V₂.1 V₂.2}
    (b : M ⟶ M') (W : (SmallEtale B S hS V₃.1)ᵒᵖ)
    (z : ((modulePushforward B S hS g).obj M).val.obj W) :
    ((modulePushforward B S hS g).map b).val.app W z =
      ((smallToposMorphismTypeU B S hS g).pushforward.map
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS V₂)).map b)).hom.app W z := rfl

/-- `AlgebraicGeometry.Space.modulePushforwardCompMap` on a local section. -/
theorem modulePushforwardCompMap_val_app (W : (SmallEtale B S hS V₃.1)ᵒᵖ)
    (z : ((modulePushforward B S hS g).obj N).val.obj W) :
    ((modulePushforward B S hS g).map al ≫
        (modulePushforwardCompIso B S hS f g).hom.app N').val.app W z =
      ((smallToposMorphismTypeU_comp B S hS f g).hom.app
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS V₁)).obj N')).hom.app W
        (((modulePushforward B S hS g).map al).val.app W z) :=
  (modules_comp_val_app B S hS ((modulePushforward B S hS g).map al)
    ((modulePushforwardCompIso B S hS f g).hom.app N') W z).trans
    (modulePushforwardCompIso_hom_app_val_app B S hS f g N' W
      (((modulePushforward B S hS g).map al).val.app W z))

/-- `AlgebraicGeometry.Space.modulePushforwardCompMap` on a local section, with the direct image
written as the direct image of sheaves of sets of [Stacks Project, Tag 03G2], part (3). -/
theorem modulePushforwardCompMap_val_app_typeU (W : (SmallEtale B S hS V₃.1)ᵒᵖ)
    (z : ((modulePushforward B S hS g).obj N).val.obj W) :
    ((modulePushforward B S hS g).map al ≫
        (modulePushforwardCompIso B S hS f g).hom.app N').val.app W z =
      ((smallToposMorphismTypeU_comp B S hS f g).hom.app
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS V₁)).obj N')).hom.app W
        (((smallToposMorphismTypeU B S hS g).pushforward.map
          ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS V₂)).map al)).hom.app W z) :=
  modulePushforwardCompMap_val_app B S hS f g al W z

/-- **The transpose of a morphism out of the inverse image along a composite**, read through the
comparison `(f ≫ g)^* ≅ f^*g^*` of [Stacks Project, Tag 03LU]: transposing
`(f ≫ g)^*M ≅ f^*g^*M ⟶ f^*N ⟶ N'` along `(f ≫ g)^* ⊣ (f ≫ g)_*` gives the transpose of
`θ : g^*M ⟶ N` followed by `g_*` of `κ : N ⟶ f_*N'` and the comparison of direct images. -/
theorem homEquiv_modulePullbackCompIso_inv_comp {M : Modules.{u, u} B S hS V₃.1 V₃.2}
    (θ : (modulePullback B S hS g).obj M ⟶ N) :
    (modulePullbackAdjunction B S hS (f ≫ g)).homEquiv _ _
        ((modulePullbackCompIso B S hS f g).inv.app M ≫ (modulePullback B S hS f).map θ ≫
          ((modulePullbackAdjunction B S hS f).homEquiv _ _).symm al) =
      (modulePullbackAdjunction B S hS g).homEquiv _ _ θ ≫ (modulePushforward B S hS g).map al ≫
        (modulePushforwardCompIso B S hS f g).hom.app N' := by
  rw [modulePullbackCompIso_eq]
  exact Adjunction.homEquiv_leftAdjointUniq_inv_comp (modulePullbackAdjunction B S hS g)
    (modulePullbackAdjunction B S hS f) (modulePushforwardCompIso B S hS f g)
    (modulePullbackAdjunction B S hS (f ≫ g)) (moduleCompAdjunction B S hS f g) rfl θ al

end Generic

section Congr

variable {X W Bas : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)
  (W₀ : ClosedSubspaces B S hS W.1) (hZ : IsFirstOrderThickening B S hS X Z.1)
  (e₀ : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
    (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS)) (qb : W ⟶ Bas)

/-- The difference of two morphisms of thickenings depends only on the two morphisms, not on the
proofs of the hypotheses. -/
theorem restrictedLiftDifferenceHom_congr {c₁ c₁' c₂ c₂' : X ⟶ W} (e₁ : c₁ = c₂) (e₂ : c₁' = c₂')
    (h₁ : subspaceInclusion B S hS X Z ≫ c₁ = e₀ ≫ subspaceInclusion B S hS W W₀)
    (h₁' : subspaceInclusion B S hS X Z ≫ c₁' = e₀ ≫ subspaceInclusion B S hS W W₀)
    (hk₁ : ∀ (V : (SmallEtale B S hS
        (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
      (x : (structureRingSheafInverseImage B S hS
        (subspaceInclusion B S hS W W₀)).obj.obj V),
      (structureSharpRingInverseImage B S hS
          (subspaceInclusion B S hS W W₀)).hom.app V x = 0 →
        (restrictedSharpThroughThickening B S hS Z W₀ c₁ e₀ h₁).hom.app V x =
          (restrictedSharpThroughThickening B S hS Z W₀ c₁' e₀ h₁').hom.app V x)
    (hc₁ : c₁ ≫ qb = c₁' ≫ qb)
    (h₂ : subspaceInclusion B S hS X Z ≫ c₂ = e₀ ≫ subspaceInclusion B S hS W W₀)
    (h₂' : subspaceInclusion B S hS X Z ≫ c₂' = e₀ ≫ subspaceInclusion B S hS W W₀)
    (hk₂ : ∀ (V : (SmallEtale B S hS
        (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
      (x : (structureRingSheafInverseImage B S hS
        (subspaceInclusion B S hS W W₀)).obj.obj V),
      (structureSharpRingInverseImage B S hS
          (subspaceInclusion B S hS W W₀)).hom.app V x = 0 →
        (restrictedSharpThroughThickening B S hS Z W₀ c₂ e₀ h₂).hom.app V x =
          (restrictedSharpThroughThickening B S hS Z W₀ c₂' e₀ h₂').hom.app V x)
    (hc₂ : c₂ ≫ qb = c₂' ≫ qb) :
    restrictedLiftDifferenceHom B S hS Z W₀ hZ e₀ qb c₁ c₁' h₁ h₁' hk₁ hc₁ =
      restrictedLiftDifferenceHom B S hS Z W₀ hZ e₀ qb c₂ c₂' h₂ h₂' hk₂ hc₂ := by
  subst e₁ e₂
  rfl

end Congr

section Target

variable {X' U' W : AlgebraicSpaces B S hS} (ZX : ClosedSubspaces B S hS X'.1)
  (ZU : ClosedSubspaces B S hS U'.1) (W₀ : ClosedSubspaces B S hS W.1)
  (hZX : IsFirstOrderThickening B S hS X' ZX.1) (hZU : IsFirstOrderThickening B S hS U' ZU.1)
  (k : U' ⟶ X')
  (k₀ : (⟨ZU.1.toFunctor, ZU.2.1⟩ : AlgebraicSpaces B S hS) ⟶
    (⟨ZX.1.toFunctor, ZX.2.1⟩ : AlgebraicSpaces B S hS))
  (hk : subspaceInclusion B S hS U' ZU ≫ k = k₀ ≫ subspaceInclusion B S hS X' ZX)
  (e : (⟨ZX.1.toFunctor, ZX.2.1⟩ : AlgebraicSpaces B S hS) ⟶
    (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS))

/-- The comparison of iterated direct images of sheaves of rings, on a local section, is the
geometric comparison of [Stacks Project, Tag 03G2], part (3), on underlying sheaves of sets. -/
theorem pushforwardRingSheafCompHom_hom_app {V₁ V₂ V₃ : AlgebraicSpaces B S hS} (f : V₁ ⟶ V₂)
    (g : V₂ ⟶ V₃) (O : Sheaf (SmallEtale.topology B S hS V₁.1) RingCat.{u})
    (V : (SmallEtale B S hS V₃.1)ᵒᵖ)
    (z : (pullbackRingSheaf.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS V₃.1)
        (smallToposMorphismTypeU B S hS g).pushforward
        (pullbackRingSheaf.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS V₂.1)
          (smallToposMorphismTypeU B S hS f).pushforward O)).obj.obj V) :
    (pushforwardRingSheafCompHom B S hS f g O).hom.app V z =
      ((smallToposMorphismTypeU_comp B S hS f g).hom.app
        ((sheafCompose (SmallEtale.topology B S hS V₁.1)
          (CategoryTheory.forget RingCat.{u})).obj O)).hom.app V z := by
  have h : (sheafCompose (SmallEtale.topology B S hS V₃.1)
      (CategoryTheory.forget RingCat.{u})).map (pushforwardRingSheafCompHom B S hS f g O) =
      (smallToposMorphismTypeU_comp B S hS f g).hom.app
        ((sheafCompose (SmallEtale.topology B S hS V₁.1)
          (CategoryTheory.forget RingCat.{u})).obj O) := by
    simp only [pushforwardRingSheafCompHom, Functor.map_comp,
      sheafCompose_map_pullbackRingSheafComp_hom]
    exact (Category.id_comp _).trans (ringSheafMap_pullbackRingSheafMapOfNatTrans _ _ _)
  exact congrFun (congrArg (fun m => m.hom.app V) h) z

/-- The naturality chase behind `AlgebraicGeometry.Space.ι_conormalPushforwardMap`, for an
arbitrary natural transformation `F ⋙ G ⟶ H`. -/
private theorem comp_naturality_chase {C₁ C₂ C₃ : Type*} [Category C₁] [Category C₂]
    [Category C₃] (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₃) (H : C₁ ⥤ C₃) (θ : F ⋙ G ⟶ H) {MX RX : C₂}
    {S T : C₁} (a : MX ⟶ F.obj S) (g : S ⟶ T) (c : MX ⟶ RX) (d : RX ⟶ F.obj T)
    (h : a ≫ F.map g = c ≫ d) :
    G.map a ≫ θ.app S ≫ H.map g = G.map c ≫ G.map d ≫ θ.app T := by
  rw [← θ.naturality g, Functor.comp_map, ← G.map_comp_assoc, h, G.map_comp_assoc]

/-- **The map of ambient sheaves of rings induced by a morphism of pairs**, on the small étale
site of `W₀`: the direct image along `e` of the comorphism of `k` read on `Z_X`, followed by the
comparison of iterated direct images. -/
def restrictedAmbientMap :
    restrictedThickeningLiftRingSheaf B S hS ZX W₀ e ⟶
      restrictedThickeningLiftRingSheaf B S hS ZU W₀ (k₀ ≫ e) :=
  (pushforwardRingFunctor (smallToposMorphismTypeU B S hS e)).map
      (restrictedSharpThroughThickening B S hS ZU ZX k k₀ hk) ≫
    pushforwardRingSheafCompHom B S hS k₀ e
      (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS U' ZU))

/-- **The map of conormal modules induced by a morphism of first order thickenings, pushed
forward to the small étale site of `W₀`**: `(e)_*𝒞_{Z_X/X'} ⟶ (k₀ ≫ e)_*𝒞_{Z_U/U'}`. -/
abbrev conormalPushforwardMap :
    (modulePushforward B S hS e).obj (conormalModule B S hS X' ZX) ⟶
      (modulePushforward B S hS (k₀ ≫ e)).obj (conormalModule B S hS U' ZU) :=
  modulePushforwardCompMap B S hS k₀ e (conormalComorphism B S hS ZX ZU hZX hZU k k₀ hk)

/-- **The defining equation of the map of conormal modules, on underlying sheaves of sets.** -/
theorem moduleSheafFunctor_map_conormalComorphism_comp :
    @CategoryStruct.comp _ _ _
        ((smallToposMorphismTypeU B S hS k₀).pushforward.obj
          ((Sheaf.moduleSheafFunctor.{u, u, u + 1} (structureRingSheafInverseImage B S hS
            (subspaceInclusion B S hS U' ZU))).obj ((SheafOfModules.restrictScalars
            (structureSharpRingInverseImage B S hS
              (subspaceInclusion B S hS U' ZU))).obj (conormalModule B S hS U' ZU)))) _
      ((Sheaf.moduleSheafFunctor.{u, u, u + 1} (structureRingSheaf B S hS
        (⟨ZX.1.toFunctor, ZX.2.1⟩ : AlgebraicSpaces B S hS))).map
        (conormalComorphism B S hS ZX ZU hZX hZU k k₀ hk))
      ((smallToposMorphismTypeU B S hS k₀).pushforward.map
        ((Sheaf.moduleSheafFunctor.{u, u, u + 1} (structureRingSheafInverseImage B S hS
          (subspaceInclusion B S hS U' ZU))).map (conormalInverseImageι B S hS ZU hZU))) =
    @CategoryStruct.comp _ _ _
        ((sheafCompose (SmallEtale.topology B S hS
          (⟨ZX.1.toFunctor, ZX.2.1⟩ : AlgebraicSpaces B S hS).1)
          (CategoryTheory.forget RingCat.{u})).obj
          (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X' ZX))) _
      ((Sheaf.moduleSheafFunctor.{u, u, u + 1} (structureRingSheafInverseImage B S hS
          (subspaceInclusion B S hS X' ZX))).map (conormalInverseImageι B S hS ZX hZX))
      ((sheafCompose (SmallEtale.topology B S hS
          (⟨ZX.1.toFunctor, ZX.2.1⟩ : AlgebraicSpaces B S hS).1)
          (CategoryTheory.forget RingCat.{u})).map
          (restrictedSharpThroughThickening B S hS ZU ZX k k₀ hk)) :=
  Sheaf.hom_ext_sections fun _ m => ι_conormalComorphism B S hS ZX ZU hZX hZU k k₀ hk m

/-- The inclusion of the ideal of values, on sections, is the direct image of the inclusion of
the conormal module on underlying sheaves of sets. -/
theorem restrictedSquareZeroValues_ι_eq_set (W₀ : ClosedSubspaces B S hS W.1)
    (hZU : IsFirstOrderThickening B S hS U' ZU.1)
    (e' : (⟨ZU.1.toFunctor, ZU.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS))
    {V : (SmallEtale B S hS (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ}
    (m : ((modulePushforward B S hS e').obj (conormalModule B S hS U' ZU)).val.obj V) :
    (restrictedSquareZeroValues B S hS ZU W₀ e' hZU).ι m =
      ((smallToposMorphismTypeU B S hS e').pushforward.map
        ((Sheaf.moduleSheafFunctor.{u, u, u + 1} (structureRingSheafInverseImage B S hS
          (subspaceInclusion B S hS U' ZU))).map (conormalInverseImageι B S hS ZU hZU))).hom.app V
        m := rfl

/-- The set-level square behind `AlgebraicGeometry.Space.ι_conormalPushforwardMap`. -/
theorem conormalPushforwardMap_set_square :
    (smallToposMorphismTypeU B S hS e).pushforward.map
        ((Sheaf.moduleSheafFunctor.{u, u, u + 1} (structureRingSheaf B S hS
          (⟨ZX.1.toFunctor, ZX.2.1⟩ : AlgebraicSpaces B S hS))).map
          (conormalComorphism B S hS ZX ZU hZX hZU k k₀ hk)) ≫
      (smallToposMorphismTypeU_comp B S hS k₀ e).hom.app
        ((Sheaf.moduleSheafFunctor.{u, u, u + 1} (structureRingSheafInverseImage B S hS
          (subspaceInclusion B S hS U' ZU))).obj ((SheafOfModules.restrictScalars
          (structureSharpRingInverseImage B S hS
            (subspaceInclusion B S hS U' ZU))).obj (conormalModule B S hS U' ZU))) ≫
      (smallToposMorphismTypeU B S hS (k₀ ≫ e)).pushforward.map
        ((Sheaf.moduleSheafFunctor.{u, u, u + 1} (structureRingSheafInverseImage B S hS
          (subspaceInclusion B S hS U' ZU))).map (conormalInverseImageι B S hS ZU hZU)) =
    (smallToposMorphismTypeU B S hS e).pushforward.map
        ((Sheaf.moduleSheafFunctor.{u, u, u + 1} (structureRingSheafInverseImage B S hS
          (subspaceInclusion B S hS X' ZX))).map (conormalInverseImageι B S hS ZX hZX)) ≫
      (smallToposMorphismTypeU B S hS e).pushforward.map
        ((sheafCompose (SmallEtale.topology B S hS
          (⟨ZX.1.toFunctor, ZX.2.1⟩ : AlgebraicSpaces B S hS).1)
          (CategoryTheory.forget RingCat.{u})).map
          (restrictedSharpThroughThickening B S hS ZU ZX k k₀ hk)) ≫
      (smallToposMorphismTypeU_comp B S hS k₀ e).hom.app
        ((sheafCompose (SmallEtale.topology B S hS
          (⟨ZU.1.toFunctor, ZU.2.1⟩ : AlgebraicSpaces B S hS).1)
          (CategoryTheory.forget RingCat.{u})).obj
          (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS U' ZU))) :=
  comp_naturality_chase (smallToposMorphismTypeU B S hS k₀).pushforward
    (smallToposMorphismTypeU B S hS e).pushforward
    (smallToposMorphismTypeU B S hS (k₀ ≫ e)).pushforward
    (smallToposMorphismTypeU_comp B S hS k₀ e).hom
    _ _ _ _ (moduleSheafFunctor_map_conormalComorphism_comp B S hS ZX ZU hZX hZU k k₀ hk)

/-- The map of ambient sheaves of rings on underlying sheaves of sets. -/
theorem sheafCompose_map_restrictedAmbientMap :
    (sheafCompose (SmallEtale.topology B S hS
        (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)
        (CategoryTheory.forget RingCat.{u})).map
        (restrictedAmbientMap B S hS ZX ZU W₀ k k₀ hk e) =
      (smallToposMorphismTypeU B S hS e).pushforward.map
          ((sheafCompose (SmallEtale.topology B S hS
            (⟨ZX.1.toFunctor, ZX.2.1⟩ : AlgebraicSpaces B S hS).1)
            (CategoryTheory.forget RingCat.{u})).map
            (restrictedSharpThroughThickening B S hS ZU ZX k k₀ hk)) ≫
        (smallToposMorphismTypeU_comp B S hS k₀ e).hom.app
          ((sheafCompose (SmallEtale.topology B S hS
            (⟨ZU.1.toFunctor, ZU.2.1⟩ : AlgebraicSpaces B S hS).1)
            (CategoryTheory.forget RingCat.{u})).obj
            (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS U' ZU))) :=
  Sheaf.hom_ext_sections fun V _ =>
    pushforwardRingSheafCompHom_hom_app B S hS k₀ e _ V _

/-- **The defining equation of the pushed-forward map of conormal modules**: on the ideals of
values, the direct image along `e` of the map of conormal modules, followed by the comparison of
iterated direct images, is `AlgebraicGeometry.Space.restrictedAmbientMap`. -/
theorem ι_conormalPushforwardMap
    {V : (SmallEtale B S hS (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ}
    (m : ((modulePushforward B S hS e).obj (conormalModule B S hS X' ZX)).val.obj V) :
    (restrictedSquareZeroValues B S hS ZU W₀ (k₀ ≫ e) hZU).ι
        (((modulePushforward B S hS e).map (conormalComorphism B S hS ZX ZU hZX hZU k k₀ hk) ≫
          (modulePushforwardCompIso B S hS k₀ e).hom.app (conormalModule B S hS U' ZU)).val.app
            V m) =
      (restrictedAmbientMap B S hS ZX ZU W₀ k k₀ hk e).hom.app V
        ((restrictedSquareZeroValues B S hS ZX W₀ e hZX).ι m) := by
  have t1 := restrictedSquareZeroValues_ι_eq_set B S hS ZU W₀ hZU (k₀ ≫ e)
    (((modulePushforward B S hS e).map (conormalComorphism B S hS ZX ZU hZX hZU k k₀ hk) ≫
          (modulePushforwardCompIso B S hS k₀ e).hom.app (conormalModule B S hS U' ZU)).val.app
            V m)
  have s2 := modulePushforwardCompMap_val_app_typeU B S hS k₀ e
    (conormalComorphism B S hS ZX ZU hZX hZU k k₀ hk) V m
  have t23 := (congrArg (((smallToposMorphismTypeU B S hS (k₀ ≫ e)).pushforward.map
        ((Sheaf.moduleSheafFunctor.{u, u, u + 1} (structureRingSheafInverseImage B S hS
          (subspaceInclusion B S hS U' ZU))).map (conormalInverseImageι B S hS ZU hZU))).hom.app V)
    (s2.trans (smallToposMorphismTypeU_comp_app_restrictScalars B S hS ZU k₀ e
      (conormalModule B S hS U' ZU) V
      (((smallToposMorphismTypeU B S hS e).pushforward.map
          ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS
            (⟨ZX.1.toFunctor, ZX.2.1⟩ : AlgebraicSpaces B S hS))).map
            (conormalComorphism B S hS ZX ZU hZX hZU k k₀ hk))).hom.app V m)))).trans
    (Sheaf.natTrans_comp_naturality_apply (smallToposMorphismTypeU B S hS k₀).pushforward
    (smallToposMorphismTypeU B S hS e).pushforward
    (smallToposMorphismTypeU B S hS (k₀ ≫ e)).pushforward
    (smallToposMorphismTypeU_comp B S hS k₀ e).hom _
    ((Sheaf.moduleSheafFunctor.{u, u, u + 1} (structureRingSheafInverseImage B S hS
          (subspaceInclusion B S hS U' ZU))).map (conormalInverseImageι B S hS ZU hZU)) V
    (((smallToposMorphismTypeU B S hS e).pushforward.map
          ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS
            (⟨ZX.1.toFunctor, ZX.2.1⟩ : AlgebraicSpaces B S hS))).map
            (conormalComorphism B S hS ZX ZU hZX hZU k k₀ hk))).hom.app V m))
  have t4 := Sheaf.map_map_hom_app_eq (smallToposMorphismTypeU B S hS e).pushforward _ _ _ _
    (moduleSheafFunctor_map_conormalComorphism_comp B S hS ZX ZU hZX hZU k k₀ hk) V m
  have t5 := congrArg (((smallToposMorphismTypeU_comp B S hS k₀ e).hom.app
        ((sheafCompose (SmallEtale.topology B S hS
          (⟨ZU.1.toFunctor, ZU.2.1⟩ : AlgebraicSpaces B S hS).1)
          (CategoryTheory.forget RingCat.{u})).obj
          (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS U' ZU)))).hom.app V) t4
  have t15 := (t1.trans t23).trans t5
  have s7 := restrictedSquareZeroValues_ι_eq_set B S hS ZX W₀ hZX e m
  have s8 := congrFun (congrArg (fun t => t.hom.app V)
    (sheafCompose_map_restrictedAmbientMap B S hS ZX ZU W₀ k k₀ hk e))
    ((restrictedSquareZeroValues B S hS ZX W₀ e hZX).ι m)
  have s9 := (congrArg ((restrictedAmbientMap B S hS ZX ZU W₀ k k₀ hk e).hom.app V) s7).trans s8
  exact t15.trans s9.symm

/-- **The difference of two morphisms of thickenings is compatible with precomposition by a
morphism of first order thickenings**, in transposed form.  Let `(k₀, k) : (Z_U ⊆ U') ⟶ (Z_X ⊆ X')`
be a morphism of first order thickenings and let `(e, c), (e, c') : (Z_X ⊆ X') ⟶ (W₀ ⊆ W)` be
two morphisms of pairs over `qb : W ⟶ Bas` satisfying hypothesis (2) of
[Stacks Project, Tag 0618].  Then the transpose `Ω_{W₀/Bas} ⟶ (k₀ ≫ e)_*𝒞_{Z_U/U'}` of the
difference of `k ≫ c` and `k ≫ c'` is the transpose `Ω_{W₀/Bas} ⟶ e_*𝒞_{Z_X/X'}` of the
difference of `c` and `c'`, followed by the map of conormal modules
`e_*𝒞_{Z_X/X'} ⟶ (k₀ ≫ e)_*𝒞_{Z_U/U'}` induced by `k`. -/
theorem homEquiv_restrictedLiftDifferenceHom_comp {Bas : AlgebraicSpaces B S hS} (qb : W ⟶ Bas)
    (c c' : X' ⟶ W)
    (h : subspaceInclusion B S hS X' ZX ≫ c = e ≫ subspaceInclusion B S hS W W₀)
    (h' : subspaceInclusion B S hS X' ZX ≫ c' = e ≫ subspaceInclusion B S hS W W₀)
    (hker : ∀ (V : (SmallEtale B S hS
        (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
      (x : (structureRingSheafInverseImage B S hS
        (subspaceInclusion B S hS W W₀)).obj.obj V),
      (structureSharpRingInverseImage B S hS
          (subspaceInclusion B S hS W W₀)).hom.app V x = 0 →
        (restrictedSharpThroughThickening B S hS ZX W₀ c e h).hom.app V x =
          (restrictedSharpThroughThickening B S hS ZX W₀ c' e h').hom.app V x)
    (hcc : c ≫ qb = c' ≫ qb)
    (h₂ : subspaceInclusion B S hS U' ZU ≫ k ≫ c = (k₀ ≫ e) ≫ subspaceInclusion B S hS W W₀)
    (h₂' : subspaceInclusion B S hS U' ZU ≫ k ≫ c' = (k₀ ≫ e) ≫ subspaceInclusion B S hS W W₀)
    (hker₂ : ∀ (V : (SmallEtale B S hS
        (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
      (x : (structureRingSheafInverseImage B S hS
        (subspaceInclusion B S hS W W₀)).obj.obj V),
      (structureSharpRingInverseImage B S hS
          (subspaceInclusion B S hS W W₀)).hom.app V x = 0 →
        (restrictedSharpThroughThickening B S hS ZU W₀ (k ≫ c) (k₀ ≫ e) h₂).hom.app V x =
          (restrictedSharpThroughThickening B S hS ZU W₀ (k ≫ c') (k₀ ≫ e) h₂').hom.app V x)
    (hcc₂ : (k ≫ c) ≫ qb = (k ≫ c') ≫ qb) :
    (modulePullbackAdjunction B S hS (k₀ ≫ e)).homEquiv _ _
        (restrictedLiftDifferenceHom B S hS ZU W₀ hZU (k₀ ≫ e) qb (k ≫ c) (k ≫ c') h₂ h₂' hker₂
          hcc₂) =
      (modulePullbackAdjunction B S hS e).homEquiv _ _
          (restrictedLiftDifferenceHom B S hS ZX W₀ hZX e qb c c' h h' hker hcc) ≫
        ((modulePushforward B S hS e).map (conormalComorphism B S hS ZX ZU hZX hZU k k₀ hk) ≫
          (modulePushforwardCompIso B S hS k₀ e).hom.app (conormalModule B S hS U' ZU)) := by
  have hf := restrictedSharpThroughThickening_comp B S hS ZX ZU k k₀ hk W₀ c e h h₂
  have hg := restrictedSharpThroughThickening_comp B S hS ZX ZU k k₀ hk W₀ c' e h' h₂'
  have key := homEquiv_liftDifferenceDifferentialsHom_eq_comp B S hS
    (subspaceInclusion B S hS W W₀ ≫ qb)
    e (k₀ ≫ e) (conormalModule B S hS X' ZX) (conormalModule B S hS U' ZU)
    (restrictedAmbientMap B S hS ZX ZU W₀ k k₀ hk e)
    (restrictedLiftDifferenceData B S hS ZX W₀ e hZX c c' h h' hker)
    (restrictedLiftDifferenceData B S hS ZU W₀ (k₀ ≫ e) hZU (k ≫ c) (k ≫ c') h₂ h₂' hker₂)
    (descend_restrictedLiftDifferenceData_structureSharpInverseImage_eq_zero
      B S hS ZX W₀ hZX e c c' h h' hker qb hcc)
    (descend_restrictedLiftDifferenceData_structureSharpInverseImage_eq_zero
      B S hS ZU W₀ hZU (k₀ ≫ e) (k ≫ c) (k ≫ c') h₂ h₂' hker₂ qb hcc₂)
    ((modulePushforward B S hS e).map (conormalComorphism B S hS ZX ZU hZX hZU k k₀ hk) ≫
          (modulePushforwardCompIso B S hS k₀ e).hom.app (conormalModule B S hS U' ZU))
    (fun m => ι_conormalPushforwardMap B S hS ZX ZU W₀ hZX hZU k k₀ hk e m)
  have k2 := key hf hg
  rw [restrictedLiftDifferenceHom_eq, restrictedLiftDifferenceHom_eq]
  convert k2 using 2

/-- **The difference of two morphisms of thickenings is compatible with precomposition by a
morphism of first order thickenings.**  In the situation of
`AlgebraicGeometry.Space.homEquiv_restrictedLiftDifferenceHom_comp`, the `𝒪_{Z_U}`-linear map

`θ(k ≫ c, k ≫ c') : (k₀ ≫ e)^*Ω_{W₀/Bas} ⟶ 𝒞_{Z_U/U'}`

of [Stacks Project, Tag 0618] with Equation (0619) is the restriction of `θ(c, c')` along
`(k₀, k)`: the comparison `(k₀ ≫ e)^* ≅ k₀^*e^*` of [Stacks Project, Tag 03LU], followed by
`k₀^*θ(c, c')` and the canonical map `k₀^*𝒞_{Z_X/X'} ⟶ 𝒞_{Z_U/U'}` of conormal modules. -/
theorem restrictedLiftDifferenceHom_comp {Bas : AlgebraicSpaces B S hS} (qb : W ⟶ Bas)
    (c c' : X' ⟶ W)
    (h : subspaceInclusion B S hS X' ZX ≫ c = e ≫ subspaceInclusion B S hS W W₀)
    (h' : subspaceInclusion B S hS X' ZX ≫ c' = e ≫ subspaceInclusion B S hS W W₀)
    (hker : ∀ (V : (SmallEtale B S hS
        (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
      (x : (structureRingSheafInverseImage B S hS
        (subspaceInclusion B S hS W W₀)).obj.obj V),
      (structureSharpRingInverseImage B S hS
          (subspaceInclusion B S hS W W₀)).hom.app V x = 0 →
        (restrictedSharpThroughThickening B S hS ZX W₀ c e h).hom.app V x =
          (restrictedSharpThroughThickening B S hS ZX W₀ c' e h').hom.app V x)
    (hcc : c ≫ qb = c' ≫ qb)
    (h₂ : subspaceInclusion B S hS U' ZU ≫ k ≫ c = (k₀ ≫ e) ≫ subspaceInclusion B S hS W W₀)
    (h₂' : subspaceInclusion B S hS U' ZU ≫ k ≫ c' = (k₀ ≫ e) ≫ subspaceInclusion B S hS W W₀)
    (hker₂ : ∀ (V : (SmallEtale B S hS
        (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
      (x : (structureRingSheafInverseImage B S hS
        (subspaceInclusion B S hS W W₀)).obj.obj V),
      (structureSharpRingInverseImage B S hS
          (subspaceInclusion B S hS W W₀)).hom.app V x = 0 →
        (restrictedSharpThroughThickening B S hS ZU W₀ (k ≫ c) (k₀ ≫ e) h₂).hom.app V x =
          (restrictedSharpThroughThickening B S hS ZU W₀ (k ≫ c') (k₀ ≫ e) h₂').hom.app V x)
    (hcc₂ : (k ≫ c) ≫ qb = (k ≫ c') ≫ qb) :
    restrictedLiftDifferenceHom B S hS ZU W₀ hZU (k₀ ≫ e) qb (k ≫ c) (k ≫ c') h₂ h₂' hker₂ hcc₂ =
      (modulePullbackCompIso B S hS k₀ e).inv.app
          (sheafOfDifferentials B S hS (subspaceInclusion B S hS W W₀ ≫ qb)) ≫
        (modulePullback B S hS k₀).map
          (restrictedLiftDifferenceHom B S hS ZX W₀ hZX e qb c c' h h' hker hcc) ≫
        ((modulePullbackAdjunction B S hS k₀).homEquiv _ _).symm
          (conormalComorphism B S hS ZX ZU hZX hZU k k₀ hk) := by
  apply ((modulePullbackAdjunction B S hS (k₀ ≫ e)).homEquiv _ _).injective
  refine (homEquiv_restrictedLiftDifferenceHom_comp B S hS ZX ZU W₀ hZX hZU k k₀ hk e qb c c' h h'
    hker hcc h₂ h₂' hker₂ hcc₂).trans ?_
  have hm := homEquiv_modulePullbackCompIso_inv_comp B S hS k₀ e
    (conormalComorphism B S hS ZX ZU hZX hZU k k₀ hk)
    (restrictedLiftDifferenceHom B S hS ZX W₀ hZX e qb c c' h h' hker hcc)
  exact hm.symm

/-- `AlgebraicGeometry.Space.restrictedLiftDifferenceHom_comp` for a restriction `e'` of the
precomposed pair that is only propositionally equal to `k₀ ≫ e`, as happens for the base changes
of a thickening to the objects of a site. -/
theorem restrictedLiftDifferenceHom_comp_of_eq {Bas : AlgebraicSpaces B S hS} (qb : W ⟶ Bas)
    (c c' : X' ⟶ W)
    (h : subspaceInclusion B S hS X' ZX ≫ c = e ≫ subspaceInclusion B S hS W W₀)
    (h' : subspaceInclusion B S hS X' ZX ≫ c' = e ≫ subspaceInclusion B S hS W W₀)
    (hker : ∀ (V : (SmallEtale B S hS
        (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
      (x : (structureRingSheafInverseImage B S hS
        (subspaceInclusion B S hS W W₀)).obj.obj V),
      (structureSharpRingInverseImage B S hS
          (subspaceInclusion B S hS W W₀)).hom.app V x = 0 →
        (restrictedSharpThroughThickening B S hS ZX W₀ c e h).hom.app V x =
          (restrictedSharpThroughThickening B S hS ZX W₀ c' e h').hom.app V x)
    (hcc : c ≫ qb = c' ≫ qb)
    (e' : (⟨ZU.1.toFunctor, ZU.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS)) (he : k₀ ≫ e = e')
    (h₂ : subspaceInclusion B S hS U' ZU ≫ k ≫ c = e' ≫ subspaceInclusion B S hS W W₀)
    (h₂' : subspaceInclusion B S hS U' ZU ≫ k ≫ c' = e' ≫ subspaceInclusion B S hS W W₀)
    (hker₂ : ∀ (V : (SmallEtale B S hS
        (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
      (x : (structureRingSheafInverseImage B S hS
        (subspaceInclusion B S hS W W₀)).obj.obj V),
      (structureSharpRingInverseImage B S hS
          (subspaceInclusion B S hS W W₀)).hom.app V x = 0 →
        (restrictedSharpThroughThickening B S hS ZU W₀ (k ≫ c) e' h₂).hom.app V x =
          (restrictedSharpThroughThickening B S hS ZU W₀ (k ≫ c') e' h₂').hom.app V x)
    (hcc₂ : (k ≫ c) ≫ qb = (k ≫ c') ≫ qb) :
    restrictedLiftDifferenceHom B S hS ZU W₀ hZU e' qb (k ≫ c) (k ≫ c') h₂ h₂' hker₂ hcc₂ =
      eqToHom (congrArg (fun t => (modulePullback B S hS t).obj
          (sheafOfDifferentials B S hS (subspaceInclusion B S hS W W₀ ≫ qb))) he.symm) ≫
      (modulePullbackCompIso B S hS k₀ e).inv.app
          (sheafOfDifferentials B S hS (subspaceInclusion B S hS W W₀ ≫ qb)) ≫
        (modulePullback B S hS k₀).map
          (restrictedLiftDifferenceHom B S hS ZX W₀ hZX e qb c c' h h' hker hcc) ≫
        ((modulePullbackAdjunction B S hS k₀).homEquiv _ _).symm
          (conormalComorphism B S hS ZX ZU hZX hZU k k₀ hk) := by
  subst he
  rw [eqToHom_refl, Category.id_comp]
  exact restrictedLiftDifferenceHom_comp B S hS ZX ZU W₀ hZX hZU k k₀ hk e qb c c' h h' hker hcc
    h₂ h₂' hker₂ hcc₂

end Target

end AlgebraicGeometry.Space

end
