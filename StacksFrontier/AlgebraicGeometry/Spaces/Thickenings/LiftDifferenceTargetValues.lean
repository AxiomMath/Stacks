module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SharpCancellation
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftDifferenceRestrictedData
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModulePushforward

/-!
# The ideal of values of a difference of comorphisms, at an arbitrary target space

Let `Z ⊂ X` be a first order thickening of algebraic spaces over a scheme `S`, with inclusion
`i : Z ⟶ X`, let `T` be an algebraic space and let `e : Z ⟶ T` be a morphism.  The direct image
`(e)_*(i^{-1}𝒪_X)` is a sheaf of rings on the small étale site of `T` whose sections commute, and
the direct image `(e)_*𝒞_{Z/X}` of the conormal module sits inside it as a square-zero ideal.

For a closed subspace `W₀ ⊆ W` and `T = W₀` this is
`AlgebraicGeometry.Space.restrictedSquareZeroValues`, by
`AlgebraicGeometry.Space.restrictedSquareZeroValues_eq`.  The properties of the ideal of values
are stated for an arbitrary pair of morphisms of sheaves of rings into the ambient sheaf.

## Main definitions

* `AlgebraicGeometry.Space.thickeningLiftRingSheafAt`: the ambient sheaf of rings
  `(e)_*(i^{-1}𝒪_X)` on the small étale site of `T`.
* `AlgebraicGeometry.Space.squareZeroValuesAt`: **the ideal of values**, a
  `Stacks.Sites.SquareZeroValues` on `(e)_*𝒞_{Z/X}` with that ambient.
* `AlgebraicGeometry.Space.sharpDiffAt`: the sectionwise difference of two morphisms of sheaves
  of rings into the ambient which agree after the reduction, read in the ideal of values.

## Main results

* `AlgebraicGeometry.Space.thickeningLiftRingSheafAt_mul_comm`: the sections of the ambient
  commute.
* `AlgebraicGeometry.Space.exists_squareZeroValuesAt_ι_sub`: the sectionwise difference of two
  morphisms agreeing after the reduction is a section of the ideal of values.
* `AlgebraicGeometry.Space.squareZeroValuesAt_ι_smul`: the action on the ideal of values of a
  scalar read through a morphism `q` is multiplication by the first of the two morphisms, as
  soon as the reduction of that morphism is `q` followed by the comorphism of `e`.
* `AlgebraicGeometry.Space.restrictedSquareZeroValues_eq`: the ideal of values
  `AlgebraicGeometry.Space.restrictedSquareZeroValues` on a closed subspace `W₀` is this one at
  `T = W₀`.

## References

* [Stacks Project, Tag 0618](https://stacks.math.columbia.edu/tag/0618), the difference of two
  lifts.
* [Stacks Project, Tag 04CN](https://stacks.math.columbia.edu/tag/04CN), the conormal module.
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU), the direct image of
  modules.
* [Stacks Project, Tag 0CKE](https://stacks.math.columbia.edu/tag/0CKE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u uu vv

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)
  (T : AlgebraicSpaces B S hS)
  (e : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ T)

/-- **The ambient sheaf of rings `(e)_*(i^{-1}𝒪_X)`** on the small étale site of `T`, in which
the comorphisms of morphisms restricting to `e` on the thickening are compared.  This is
`AlgebraicGeometry.Space.restrictedThickeningLiftRingSheaf` with the closed subspace `W₀`
replaced by an arbitrary algebraic space. -/
noncomputable abbrev thickeningLiftRingSheafAt :=
  pullbackRingSheaf.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS T.1)
    (smallToposMorphismTypeU B S hS e).pushforward
    (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z))

/-- The sections of the ambient sheaf of rings commute. -/
theorem thickeningLiftRingSheafAt_mul_comm {V : (SmallEtale B S hS T.1)ᵒᵖ}
    (s t : (thickeningLiftRingSheafAt B S hS Z T e).obj.obj V) :
    s * t = t * s :=
  pullback_sections_mul_comm
    (R := structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z))
    (SmallEtale.topology B S hS T.1)
    (smallToposMorphismTypeU B S hS e).pushforward
    (pullback_sections_mul_comm (R := structureRingSheaf B S hS X)
      (SmallEtale.topology B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1)
      (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z)).inverseImage
      (ringSheaf_mul_comm_smallEtaleRingedSite B S hS X)) V s t

variable (hZ : IsFirstOrderThickening B S hS X Z.1)

/-- **The ideal of values at an arbitrary target space**: the direct image along `e` of the
conormal module of the first order thickening `Z ⊂ X`, included into the direct image along `e`
of `i^{-1}𝒪_X` as an ideal of square zero.  The inclusion is the direct image of
`AlgebraicGeometry.Space.conormalInverseImageι`, and its injectivity and square-zero property
cross the direct image because the direct image of sheaves of sets is left exact. -/
def squareZeroValuesAt :
    Stacks.Sites.SquareZeroValues
      ((modulePushforward B S hS e).obj (conormalModule B S hS X Z)) :=
  haveI := preservesFiniteLimits_smallToposMorphismTypeU_pushforward B S hS e
  { ambient := thickeningLiftRingSheafAt B S hS Z T e
    ambient_mul_comm := thickeningLiftRingSheafAt_mul_comm B S hS Z T e
    ι := fun {V} => ((pullbackModuleMap (SmallEtale.topology B S hS T.1)
        (smallToposMorphismTypeU B S hS e).pushforward
        (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z))
        (conormalInverseImageι B S hS Z hZ)).val.app V).hom.toAddMonoidHom
    ι_injective := fun {V} =>
      injective_app_pullbackModuleMap (SmallEtale.topology B S hS T.1)
        (smallToposMorphismTypeU B S hS e).pushforward
        (conormalInverseImageι B S hS Z hZ) V
        (conormalInverseImageι_injective B S hS Z hZ)
    ι_map := fun {_ _} h m =>
      PresheafOfModules.naturality_apply
        (pullbackModuleMap (SmallEtale.topology B S hS T.1)
          (smallToposMorphismTypeU B S hS e).pushforward
          (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z))
          (conormalInverseImageι B S hS Z hZ)).val h m
    mul_ι_eq_zero := fun {V} m m' =>
      mul_app_pullbackModuleMap_eq_zero (SmallEtale.topology B S hS T.1)
        (smallToposMorphismTypeU B S hS e).pushforward
        (conormalInverseImageι B S hS Z hZ) V
        (mul_app_conormalInverseImageι_eq_zero B S hS Z hZ) m m' }

/-- **The inclusion of the ideal of values on sections**: the direct image along `e` of the
inclusion of the conormal module into `i^{-1}𝒪_X`. -/
theorem squareZeroValuesAt_ι {V : (SmallEtale B S hS T.1)ᵒᵖ}
    (m : ((modulePushforward B S hS e).obj (conormalModule B S hS X Z)).val.obj V) :
    (squareZeroValuesAt B S hS Z T e hZ).ι m =
      ((pullbackModuleMap (SmallEtale.topology B S hS T.1)
          (smallToposMorphismTypeU B S hS e).pushforward
          (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z))
          (conormalInverseImageι B S hS Z hZ)).val.app V).hom m :=
  rfl

section Pair

variable {A : Sheaf (SmallEtale.topology B S hS T.1) RingCat.{u}}

/-- The reduction `i^{-1}𝒪_X ⟶ 𝒪_Z` pushed forward along `e`, which the two morphisms into the
ambient sheaf of rings are required to agree after. -/
noncomputable abbrev thickeningLiftReductionAt :
    thickeningLiftRingSheafAt B S hS Z T e ⟶
      pullbackRingSheaf.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS T.1)
        (smallToposMorphismTypeU B S hS e).pushforward
        (structureRingSheaf B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)) :=
  pullbackRingSheafMap (SmallEtale.topology B S hS T.1)
    (smallToposMorphismTypeU B S hS e).pushforward
    (structureSharpRingInverseImage B S hS (subspaceInclusion B S hS X Z))

/-- **The sectionwise difference of two morphisms agreeing after the reduction is a section of
the ideal of values.**  The difference is killed by the pushed-forward reduction, and a section
of `(e)_*(i^{-1}𝒪_X)` killed by it is in the image of `(e)_*𝒞_{Z/X}`, the conormal module being
exactly the kernel of the reduction. -/
theorem exists_squareZeroValuesAt_ι_sub
    (F G : A ⟶ thickeningLiftRingSheafAt B S hS Z T e)
    (hFG : F ≫ thickeningLiftReductionAt B S hS Z T e =
      G ≫ thickeningLiftReductionAt B S hS Z T e)
    (V : (SmallEtale B S hS T.1)ᵒᵖ) (x : A.obj.obj V) :
    ∃ m : ((modulePushforward B S hS e).obj (conormalModule B S hS X Z)).val.obj V,
      (squareZeroValuesAt B S hS Z T e hZ).ι m = F.hom.app V x - G.hom.app V x :=
  haveI := preservesFiniteLimits_smallToposMorphismTypeU_pushforward B S hS e
  exists_app_pullbackModuleMap_eq (SmallEtale.topology B S hS T.1)
    (smallToposMorphismTypeU B S hS e).pushforward
    (conormalInverseImageι B S hS Z hZ)
    (structureSharpRingInverseImage B S hS (subspaceInclusion B S hS X Z)) V
    (app_conormalInverseImageι_eq_zero B S hS Z hZ)
    (conormalInverseImageι_injective B S hS Z hZ)
    (exists_conormalInverseImageι_eq B S hS Z hZ) _
    (Stacks.Sites.sub_mem_ker_of_comp_eq _ _ _ hFG V x)

/-- **The action on the ideal of values is multiplication by the first morphism.**  A scalar
read through `q` acts on `(e)_*𝒞_{Z/X}` through the comorphism of `e`, and the first of the two
morphisms has that same image under the reduction; so the two actions agree, and the inclusion
of the ideal of values is linear for the multiplication of the ambient sheaf of rings. -/
theorem squareZeroValuesAt_ι_smul (q : A ⟶ structureRingSheaf B S hS T)
    (F : A ⟶ thickeningLiftRingSheafAt B S hS Z T e)
    (hF : F ≫ thickeningLiftReductionAt B S hS Z T e = q ≫ structureSharp B S hS e)
    {V : (SmallEtale B S hS T.1)ᵒᵖ} (x : A.obj.obj V)
    (m : ((modulePushforward B S hS e).obj (conormalModule B S hS X Z)).val.obj V) :
    letI : Module ((structureRingSheaf B S hS T).obj.obj V)
        (((modulePushforward B S hS e).obj (conormalModule B S hS X Z)).val.obj V) :=
      (((modulePushforward B S hS e).obj (conormalModule B S hS X Z)).val.obj V).isModule
    (squareZeroValuesAt B S hS Z T e hZ).ι (q.hom.app V x • m) =
      (show ToType ((squareZeroValuesAt B S hS Z T e hZ).ambient.obj.obj V) from
          F.hom.app V x) *
        (squareZeroValuesAt B S hS Z T e hZ).ι m :=
  (congrArg (squareZeroValuesAt B S hS Z T e hZ).ι
      (smul_restrictScalars_pullbackModuleObj (SmallEtale.topology B S hS T.1)
        (smallToposMorphismTypeU B S hS e).pushforward
        (structureSharpRingInverseImage B S hS (subspaceInclusion B S hS X Z))
        (conormalModule B S hS X Z) (structureSharp B S hS e) V _ _
        (ConcreteCategory.congr_hom (congrArg (fun n => n.hom.app V) hF) x) m)).trans
    (mul_app_pullbackModuleMap (SmallEtale.topology B S hS T.1)
      (smallToposMorphismTypeU B S hS e).pushforward
      (conormalInverseImageι B S hS Z hZ) V _ m)

/-- **The sectionwise difference of two morphisms agreeing after the reduction, read in the
ideal of values**: the preimage supplied by
`AlgebraicGeometry.Space.exists_squareZeroValuesAt_ι_sub`, pinned by
`AlgebraicGeometry.Space.squareZeroValuesAt_ι_sharpDiffAt`.  The choice is unique, the inclusion
of the ideal of values being injective on sections. -/
def sharpDiffAt (F G : A ⟶ thickeningLiftRingSheafAt B S hS Z T e)
    (hFG : F ≫ thickeningLiftReductionAt B S hS Z T e =
      G ≫ thickeningLiftReductionAt B S hS Z T e)
    {V : (SmallEtale B S hS T.1)ᵒᵖ} (x : A.obj.obj V) :
    ((modulePushforward B S hS e).obj (conormalModule B S hS X Z)).val.obj V :=
  (exists_squareZeroValuesAt_ι_sub B S hS Z T e hZ F G hFG V x).choose

/-- The defining equation of `AlgebraicGeometry.Space.sharpDiffAt`. -/
theorem squareZeroValuesAt_ι_sharpDiffAt
    (F G : A ⟶ thickeningLiftRingSheafAt B S hS Z T e)
    (hFG : F ≫ thickeningLiftReductionAt B S hS Z T e =
      G ≫ thickeningLiftReductionAt B S hS Z T e)
    {V : (SmallEtale B S hS T.1)ᵒᵖ} (x : A.obj.obj V) :
    (squareZeroValuesAt B S hS Z T e hZ).ι
        (sharpDiffAt B S hS Z T e hZ F G hFG x) =
      F.hom.app V x - G.hom.app V x :=
  (exists_squareZeroValuesAt_ι_sub B S hS Z T e hZ F G hFG V x).choose_spec

end Pair

/-! ### A function vanishing on the target of a factor kills the direct image -/

section Annihilation

variable {T' Yy : AlgebraicSpaces B S hS}

/-- A section killed by a morphism of sheaves of rings is killed by every composite with it. -/
private theorem app_comp_eq_zero {Cc : Type uu} [Category.{vv} Cc] {Jc : GrothendieckTopology Cc}
    {A Bb D : Sheaf Jc RingCat.{u}} (a : A ⟶ Bb) (ψ : Bb ⟶ D) {V : Ccᵒᵖ} (z : A.obj.obj V)
    (hz : a.hom.app V z = 0) : (a ≫ ψ).hom.app V z = 0 := by
  change (ψ.hom.app V) ((a.hom.app V) z) = 0
  rw [hz, map_zero]

/-- Equal morphisms of sheaves of rings agree on every section. -/
theorem ringSheafHom_congr_app_apply {Cc : Type uu} [Category.{vv} Cc]
    {Jc : GrothendieckTopology Cc} {A Bb : Sheaf Jc RingCat.{u}} {a b : A ⟶ Bb} (h : a = b)
    (V : Ccᵒᵖ) (z : A.obj.obj V) : a.hom.app V z = b.hom.app V z :=
  ConcreteCategory.congr_hom (NatTrans.congr_app (congrArg (fun m : A ⟶ Bb => m.hom) h) V) z

/-- **A section of `𝒪_Y` killed by the comorphism of `g : T' ⟶ Y` kills every direct image
along a morphism factoring through `g`.**  The comorphism of `f ≫ g` is the comorphism of `g`
followed by the direct image of the comorphism of `f`, by the compatibility of
[Stacks Project, Tag 03G8] with composition, so a section killed by the latter is killed by the
former; and the direct image of modules is restriction of scalars along it, so such a section
acts by zero.

This is `AlgebraicGeometry.Space.annihilatedByKerIdeal_modulePushforward` — part (3) of
[Stacks Project, Tag 04CJ] — read at a composite. -/
theorem structureSharp_comp_app_eq_zero {Z' : AlgebraicSpaces B S hS} (f : Z' ⟶ T')
    (g : T' ⟶ Yy) (V : (SmallEtale B S hS Yy.1)ᵒᵖ)
    (z : ToType ((structureRingSheaf B S hS Yy).obj.obj V))
    (hz : (structureSharp B S hS g).hom.app V z = 0) :
    (structureSharp B S hS (f ≫ g)).hom.app V z = 0 :=
  (ringSheafHom_congr_app_apply (structureSharp_comp B S hS f g) V z).symm.trans
    (app_comp_eq_zero _ _ z hz)

/-- A section `z` of `𝒪_Y` killed by the comorphism of `g : T' ⟶ Y` acts by zero on every section
of the direct image `(f ≫ g)_* N` of an `𝒪_{Z'}`-module `N`. -/
theorem smul_modulePushforward_comp_eq_zero {Z' : AlgebraicSpaces B S hS} (f : Z' ⟶ T')
    (g : T' ⟶ Yy) (N : Modules B S hS Z'.1 Z'.2)
    (V : (SmallEtale B S hS Yy.1)ᵒᵖ)
    (z : ToType ((structureRingSheaf B S hS Yy).obj.obj V))
    (hz : (structureSharp B S hS g).hom.app V z = 0)
    (m : ((modulePushforward B S hS (f ≫ g)).obj N).val.obj V) :
    letI : Module ((structureRingSheaf B S hS Yy).obj.obj V)
        (((modulePushforward B S hS (f ≫ g)).obj N).val.obj V) :=
      (((modulePushforward B S hS (f ≫ g)).obj N).val.obj V).isModule
    z • m = 0 :=
  Stacks.Sheaves.PushforwardEssentialImage.smul_restrictScalars_eq_zero
    (structureSharp B S hS (f ≫ g)) ((moduleDirectImage B S hS (f ≫ g)).obj N) V z
    (structureSharp_comp_app_eq_zero B S hS f g V z hz) m

end Annihilation

/-! ### Agreement on the kernel of the reduction, from agreement after the unit -/

section Descent

variable (hZfo : IsFirstOrderThickening B S hS X Z.1)

/-- **The transport of the conormal inclusion is the unit at a section of `𝒪_X` vanishing on
`Z`.**  This is `Stacks.SheafOfModules.IdealTransport.map_idealι` read on sections: the
transport of `𝒞_{Z/X} ⟶ i^{-1}𝒪_X` is the inclusion of the kernel ideal of
`i^♯ : 𝒪_X ⟶ i_*𝒪_Z` read through the unit `𝒪_X ≅ i_*i^{-1}𝒪_X`. -/
theorem exists_app_thickeningRingUnit_eq (V : (SmallEtale B S hS X.1)ᵒᵖ)
    (m : ((thickeningTransport B S hS Z).obj
      ((SheafOfModules.restrictScalars (structureSharpRingInverseImage B S hS
        (subspaceInclusion B S hS X Z))).obj (conormalModule B S hS X Z))).val.obj V) :
    ∃ a : ToType ((structureRingSheaf B S hS X).obj.obj V),
      (structureSharp B S hS (subspaceInclusion B S hS X Z)).hom.app V a = 0 ∧
        ((smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z)).pushforward.map
            ((CategoryTheory.Sheaf.moduleSheafFunctor
              (structureRingSheafInverseImage B S hS
                (subspaceInclusion B S hS X Z))).map
              (conormalInverseImageι B S hS Z hZfo))).hom.app V m =
          (thickeningRingUnit B S hS Z).hom.app V a :=
  ⟨((conormalDirectImageIso B S hS Z hZfo).inv.val.app V m).1,
    RingHom.mem_ker.1 ((SheafOfModules.mem_kerIdeal
        (structureSharp B S hS (subspaceInclusion B S hS X Z)) V _).1
      ((conormalDirectImageIso B S hS Z hZfo).inv.val.app V m).2),
    SheafOfModules.hom_congr_app_apply
      (Stacks.SheafOfModules.IdealTransport.map_idealι
        (hηiso := isIso_thickeningRingUnit B S hS Z hZfo.1)
        (SmallEtale.topology B S hS X.1) (thickeningToposHom B S hS Z).pushforward
        (structureSharpRingInverseImage B S hS (subspaceInclusion B S hS X Z))
        (thickeningRingUnit B S hS Z)
        (structureSharp B S hS (subspaceInclusion B S hS X Z))
        (conormalDirectImageIso B S hS Z hZfo)) V m⟩

/-- The direct image of a morphism of sheaves of rings is, on sections, the direct image of its
underlying morphism of sheaves of sets. -/
private theorem app_pushforwardRingFunctor_map
    {Aa : Sheaf (SmallEtale.topology B S hS
      (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1) RingCat.{u}}
    (ψ : structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z) ⟶ Aa)
    (V' : (SmallEtale B S hS X.1)ᵒᵖ)
    (w : ToType ((pullbackRingSheaf.{u, u, u, u + 1, u, u + 1}
      (SmallEtale.topology B S hS X.1)
      (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z)).pushforward
      (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z))).obj.obj V')) :
    ((pushforwardRingFunctor (smallToposMorphismTypeU B S hS
          (subspaceInclusion B S hS X Z))).map ψ).hom.app V' w =
      ((smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z)).pushforward.map
        ((sheafCompose (SmallEtale.topology B S hS
          (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1)
          (CategoryTheory.forget RingCat.{u})).map ψ)).hom.app V' w :=
  setSheafHom_congr_app_apply
    (ringSheafMap_pullbackRingSheafMap (SmallEtale.topology B S hS X.1)
      (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z)).pushforward ψ) V' w

include hZfo in
/-- **The direct images of two morphisms of sheaves of rings agree after the direct image of the
conormal inclusion.**  On sections over the small étale site of `X` the transport of the
conormal inclusion is the unit at a section of `𝒪_X` vanishing on `Z`, by
`AlgebraicGeometry.Space.exists_app_thickeningRingUnit_eq`, and the hypothesis says the two
morphisms agree there. -/
theorem pushforward_map_conormalInverseImageι_comp_eq
    {Aa : Sheaf (SmallEtale.topology B S hS
      (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1) RingCat.{u}}
    (f g : structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z) ⟶ Aa)
    (hfg : ∀ (V : (SmallEtale B S hS X.1)ᵒᵖ)
      (a : ToType ((structureRingSheaf B S hS X).obj.obj V)),
      (structureSharp B S hS (subspaceInclusion B S hS X Z)).hom.app V a = 0 →
      (thickeningRingUnit B S hS Z ≫
          (pushforwardRingFunctor (smallToposMorphismTypeU B S hS
            (subspaceInclusion B S hS X Z))).map f).hom.app V a =
        (thickeningRingUnit B S hS Z ≫
          (pushforwardRingFunctor (smallToposMorphismTypeU B S hS
            (subspaceInclusion B S hS X Z))).map g).hom.app V a) :
    (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z)).pushforward.map
          ((CategoryTheory.Sheaf.moduleSheafFunctor
            (structureRingSheafInverseImage B S hS
              (subspaceInclusion B S hS X Z))).map
            (conormalInverseImageι B S hS Z hZfo)) ≫
        (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z)).pushforward.map
          ((sheafCompose (SmallEtale.topology B S hS
            (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1)
            (CategoryTheory.forget RingCat.{u})).map f) =
      (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z)).pushforward.map
          ((CategoryTheory.Sheaf.moduleSheafFunctor
            (structureRingSheafInverseImage B S hS
              (subspaceInclusion B S hS X Z))).map
            (conormalInverseImageι B S hS Z hZfo)) ≫
        (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z)).pushforward.map
          ((sheafCompose (SmallEtale.topology B S hS
            (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1)
            (CategoryTheory.forget RingCat.{u})).map g) :=
  CategoryTheory.Sheaf.hom_ext_sections fun V' m' => by
    obtain ⟨a, ha, hau⟩ := exists_app_thickeningRingUnit_eq B S hS Z hZfo V' m'
    have key (h : structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z) ⟶ Aa) :
        ((smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z)).pushforward.map
          ((sheafCompose (SmallEtale.topology B S hS
            (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1)
            (CategoryTheory.forget RingCat.{u})).map h)).hom.app V' _ =
        (thickeningRingUnit B S hS Z ≫ (pushforwardRingFunctor (smallToposMorphismTypeU B S hS
          (subspaceInclusion B S hS X Z))).map h).hom.app V' a :=
      (congrArg _ hau).trans (app_pushforwardRingFunctor_map B S hS Z h V' _).symm
    exact (key f).trans ((hfg V' a ha).trans (key g).symm)

include hZfo in
/-- **Two morphisms of sheaves of rings on the small étale site of a first order thickening
agree on the sections killed by the reduction `i^♯ : i^{-1}𝒪_X ⟶ 𝒪_Z`, as soon as their direct
images agree at the unit of every section of `𝒪_X` vanishing on `Z`.**

Every section killed by the reduction comes from the conormal module
(`AlgebraicGeometry.Space.exists_conormalInverseImageι_eq`), and the direct image of sheaves of
sets along the inclusion of a closed subspace is faithful, so the agreement of the direct images
of `AlgebraicGeometry.Space.pushforward_map_conormalInverseImageι_comp_eq` descends. -/
theorem app_eq_of_app_eq_zero_of_app_thickeningRingUnit_eq
    {Aa : Sheaf (SmallEtale.topology B S hS
      (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1) RingCat.{u}}
    (f g : structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z) ⟶ Aa)
    (hfg : ∀ (V : (SmallEtale B S hS X.1)ᵒᵖ)
      (a : ToType ((structureRingSheaf B S hS X).obj.obj V)),
      (structureSharp B S hS (subspaceInclusion B S hS X Z)).hom.app V a = 0 →
      (thickeningRingUnit B S hS Z ≫
          (pushforwardRingFunctor (smallToposMorphismTypeU B S hS
            (subspaceInclusion B S hS X Z))).map f).hom.app V a =
        (thickeningRingUnit B S hS Z ≫
          (pushforwardRingFunctor (smallToposMorphismTypeU B S hS
            (subspaceInclusion B S hS X Z))).map g).hom.app V a)
    (V : (SmallEtale B S hS
      (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
    (x : ToType ((structureRingSheafInverseImage B S hS
      (subspaceInclusion B S hS X Z)).obj.obj V))
    (hx : (structureSharpRingInverseImage B S hS
      (subspaceInclusion B S hS X Z)).hom.app V x = 0) :
    f.hom.app V x = g.hom.app V x := by
  obtain ⟨m, hm⟩ := exists_conormalInverseImageι_eq B S hS Z hZfo V x hx
  have := (fullyFaithfulSmallEtalePushforwardOfIsClosedImmersion B S hS
    (subspaceInclusion B S hS X Z) Z.2.2).faithful
  rw [← hm]
  exact setSheafHom_congr_app_apply
    (((smallToposMorphismTypeU B S hS
        (subspaceInclusion B S hS X Z)).pushforward).map_injective
      (((smallToposMorphismTypeU B S hS
          (subspaceInclusion B S hS X Z)).pushforward.map_comp _ _).trans
        ((pushforward_map_conormalInverseImageι_comp_eq B S hS Z hZfo f g hfg).trans
          (((smallToposMorphismTypeU B S hS
            (subspaceInclusion B S hS X Z)).pushforward.map_comp _ _).symm)))) V m

end Descent

/-! ### Agreement with the construction on a closed subspace of the target -/

section Restricted

variable {W : AlgebraicSpaces B S hS} (W₀ : ClosedSubspaces B S hS W.1)
  (e₀ : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
    (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS))

/-- **The ideal of values `AlgebraicGeometry.Space.restrictedSquareZeroValues` on a closed
subspace `W₀` is `AlgebraicGeometry.Space.squareZeroValuesAt` at `T = W₀`.** -/
theorem restrictedSquareZeroValues_eq :
    restrictedSquareZeroValues B S hS Z W₀ e₀ hZ =
      squareZeroValuesAt B S hS Z
        (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS) e₀ hZ :=
  rfl

end Restricted

end AlgebraicGeometry.Space

end
