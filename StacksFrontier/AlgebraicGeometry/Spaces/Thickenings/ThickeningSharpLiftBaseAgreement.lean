module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ThickeningSharpRestrictedLift
public import StacksFrontier.AlgebraicGeometry.Spaces.LiftDifferenceSurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftDifferenceTargetValues

/-!
# A solution of the lifting problem agrees with a given one on the functions read from a base

Let `Z ⊆ X` be a thickening of algebraic spaces over a scheme `S` with inclusion `i : Z ⟶ X`,
let `W₀ ⊆ W` be a closed subspace with inclusion `j : W₀ ⟶ W` and let `e₀ : Z ⟶ W₀`.
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/ThickeningSharpRestrictedLift.lean` carries a
solution

`g : j^{-1}𝒪_W ⟶ (e₀)_*(i^{-1}𝒪_X)`

of the lifting problem on the small étale site of `W₀` back to a morphism
`𝒪_W ⟶ (e₀ ≫ j)_*(i^{-1}𝒪_X)` on the site of `W`, which is the form read on étale scheme
charts.

The hypothesis under which that chart reading is a morphism *over the base* —
`AlgebraicGeometry.Space.exists_thickeningLiftChartSiteHom_of_index` — is that the carried-back
morphism agrees with the comorphism of a known morphism `c : X ⟶ W` on the regular functions
read from a space `W'` under `W`.  This file supplies that agreement from the two facts a
solution produced by [Stacks Project, Tag 0618] carries:

* the carrying back is **natural**: precomposing it with any morphism `a : A' ⟶ 𝒪_W` of sheaves
  of rings on the site of `W` depends on `g` only through `j^{-1}(a) ≫ g`, because the unit of
  `j^{-1} ⊣ j_*` is natural; and
* a solution of the shape `f - ι ∘ D ∘ q` of
  `Stacks.Sites.derivationActionHom` agrees with `f` after any morphism whose values `q` carries
  into the kernel of the derivation `D`.

Composing the two, a solution obtained by moving a known comorphism by the derivation attached
to an `𝒪_X`-linear map agrees with that comorphism on every function read from `W'`, since such
a function is a value of `r^♯` and the derivation of Equation [Stacks Project, Tag 0619] kills
those.

## Main results

* `Stacks.Sites.comp_derivationActionHom_eq`: **the modified lift agrees with the lift after a
  morphism whose values are killed by the derivation**, and
  `AlgebraicGeometry.Space.comp_liftDifferenceDataOfHom_g_eq`, the same for the pair of lifts
  attached to an `𝒪_X`-linear map.
* `AlgebraicGeometry.Space.comp_liftRestrictedSharpThroughThickening_congr`: **the carried-back
  solution composed with a morphism of sheaves of rings depends on the solution only through its
  inverse image.**
* `Space.structureSharpRingInverseImage_comp_liftRestrictedSharpThroughThickening_eq`: **the
  hypothesis of `AlgebraicGeometry.Space.exists_thickeningLiftChartSiteHom_of_index`**, at the
  level of morphisms of sheaves of rings, and
  `AlgebraicGeometry.Space.app_liftRestrictedSharpThroughThickening_eq`, the same read on a section
  over an étale chart.

## Implementation notes

Every rearrangement of composites is a tiny `private` lemma over an abstract category with each
morphism a variable, as the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/LiftDifferenceSection.lean` require:
`rw [Category.assoc]` on these geometric terms is a deterministic `whnf` timeout.

The agreement is proved at the level of *morphisms of sheaves of rings* and only then read on a
section.  The alternative — computing the sections of the direct image of `g` over a chart —
would need a chart-level description of the sections of a direct image along a closed immersion,
which the development does not have; the naturality of the unit needs none.

**No `@[stacks]` attribute is placed.**  This is a comparison internal to this development of
two readings of [Stacks Project, Tag 03G8].

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8), the structure map.
* [Stacks Project, Tag 0618](https://stacks.math.columbia.edu/tag/0618), the correspondence
  between lifts and linear maps.
* [Stacks Project, Tag 0619](https://stacks.math.columbia.edu/tag/0619), the derivation attached
  to a linear map.
* [Stacks Project, Tag 0CKE](https://stacks.math.columbia.edu/tag/0CKE), the tag this step is an
  input of.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u uu vv

namespace Stacks.Sites

variable {Cc : Type uu} [Category.{vv} Cc] {J : GrothendieckTopology Cc}
  {A O : Sheaf J RingCat.{u}} {q : A ⟶ O} {M : SheafOfModules.{u} O}
  (E : SquareZeroValues M) (f : A ⟶ E.ambient)
  (D : ∀ V : Ccᵒᵖ, O.obj.obj V →+ M.val.obj V)
  (hmul : ∀ (V : Ccᵒᵖ) (s t : O.obj.obj V), D V (s * t) = s • D V t + t • D V s)
  (hmap : ∀ (V W : Ccᵒᵖ) (h : V ⟶ W) (s : O.obj.obj V),
    D W (O.obj.map h s) = M.val.map h (D V s))
  (ι_smul : ∀ (V : Ccᵒᵖ) (x : A.obj.obj V) (m : M.val.obj V),
    E.ι (q.hom.app V x • m) = f.hom.app V x * E.ι m)

/-- **The lift modified by a derivation agrees with the lift after a morphism whose values `q`
carries into the kernel of the derivation.**  The two differ sectionwise by `ι (D (q x))`, and
that vanishes at every section in the image of such a morphism.

This is hypothesis (2) of [Stacks Project, Tag 0618] for a *base*, rather than for the defining
ideal of the thickening: the modified lift is again a lift over `W'` as soon as the derivation
kills the functions read from `W'`. -/
theorem comp_derivationActionHom_eq {A' : Sheaf J RingCat.{u}} (ψ : A' ⟶ A)
    (hD : ∀ (V : Ccᵒᵖ) (x : A'.obj.obj V), D V (q.hom.app V (ψ.hom.app V x)) = 0) :
    ψ ≫ derivationActionHom E f D hmul hmap ι_smul = ψ ≫ f :=
  Sheaf.hom_ext (NatTrans.ext (funext fun V ↦ RingCat.hom_ext (RingHom.ext fun x ↦ by
    change f.hom.app V (ψ.hom.app V x) -
        E.ι (D V (q.hom.app V (ψ.hom.app V x))) = f.hom.app V (ψ.hom.app V x)
    rw [hD V x, map_zero, sub_zero])))

end Stacks.Sites

namespace AlgebraicGeometry.Space

open Stacks.Sites

/-! ### Rearrangements -/

/-- Reassociating a composite of four morphisms to the left. -/
private theorem comp_assoc_left' {Cc : Type*} [Category Cc] {A₁ A₂ A₃ A₄ A₅ : Cc}
    (u : A₁ ⟶ A₂) (v : A₂ ⟶ A₃) (w : A₃ ⟶ A₄) (z : A₄ ⟶ A₅) :
    u ≫ ((v ≫ w) ≫ z) = ((u ≫ v) ≫ w) ≫ z := by
  simp only [Category.assoc]

/-- Reassociating the first three factors of a composite of four morphisms to the right. -/
private theorem comp_assoc_right' {Cc : Type*} [Category Cc] {A₁ A₂ A₃ A₄ A₅ : Cc}
    (u : A₁ ⟶ A₂) (v : A₂ ⟶ A₃) (w : A₃ ⟶ A₄) (z : A₄ ⟶ A₅) :
    ((u ≫ v) ≫ w) ≫ z = (u ≫ (v ≫ w)) ≫ z := by
  simp only [Category.assoc]

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X W : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)
  (W₀ : ClosedSubspaces B S hS W.1)

/-! ### The carrying back is natural -/

/-- **The carried-back solution, composed with a morphism of sheaves of rings on the site of
`W`, depends on the solution only through its inverse image along `j`.**

The carrying back is the unit of `j^{-1} ⊣ j_*` followed by the direct image of the solution and
by the comparison of iterated direct images; the unit is natural, so precomposition with
`a : A' ⟶ 𝒪_W` turns the direct image of `g` into the direct image of `j^{-1}(a) ≫ g`. -/
theorem comp_liftRestrictedSharpThroughThickening_congr
    (e₀ : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS))
    {A' : Sheaf (SmallEtale.topology B S hS W.1) RingCat.{u}}
    (a : A' ⟶ structureRingSheaf B S hS W)
    (g g' : structureRingSheafInverseImage B S hS (subspaceInclusion B S hS W W₀) ⟶
      restrictedThickeningLiftRingSheaf B S hS Z W₀ e₀)
    (h : (inverseImageRingFunctor (smallToposMorphismTypeU B S hS
            (subspaceInclusion B S hS W W₀))).map a ≫ g =
        (inverseImageRingFunctor (smallToposMorphismTypeU B S hS
            (subspaceInclusion B S hS W W₀))).map a ≫ g') :
    a ≫ liftRestrictedSharpThroughThickening B S hS Z W₀ e₀ g =
      a ≫ liftRestrictedSharpThroughThickening B S hS Z W₀ e₀ g' := by
  have hnat : a ≫ ringUnit (smallToposMorphismTypeU B S hS
          (subspaceInclusion B S hS W W₀)) (structureRingSheaf B S hS W) =
      ringUnit (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS W W₀)) A' ≫
        (pushforwardRingFunctor (smallToposMorphismTypeU B S hS
          (subspaceInclusion B S hS W W₀))).map
          ((inverseImageRingFunctor (smallToposMorphismTypeU B S hS
            (subspaceInclusion B S hS W W₀))).map a) :=
    (ringUnitNatTrans (smallToposMorphismTypeU B S hS
      (subspaceInclusion B S hS W W₀))).naturality a
  have key : ∀ gg : structureRingSheafInverseImage B S hS
        (subspaceInclusion B S hS W W₀) ⟶ restrictedThickeningLiftRingSheaf B S hS Z W₀ e₀,
      a ≫ liftRestrictedSharpThroughThickening B S hS Z W₀ e₀ gg =
        (ringUnit (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS W W₀)) A' ≫
            (pushforwardRingFunctor (smallToposMorphismTypeU B S hS
              (subspaceInclusion B S hS W W₀))).map
              ((inverseImageRingFunctor (smallToposMorphismTypeU B S hS
                (subspaceInclusion B S hS W W₀))).map a ≫ gg)) ≫
          pushforwardRingSheafCompHom B S hS e₀ (subspaceInclusion B S hS W W₀)
            (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z)) := by
    intro gg
    refine Eq.trans (comp_assoc_left' a _ _ _) ?_
    refine Eq.trans (congrArg (fun m ↦ (m ≫ (pushforwardRingFunctor
        (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS W W₀))).map gg) ≫
      pushforwardRingSheafCompHom B S hS e₀ (subspaceInclusion B S hS W W₀)
        (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z))) hnat) ?_
    refine Eq.trans (comp_assoc_right' _ _ _ _) ?_
    exact congrArg (fun m ↦ (ringUnit (smallToposMorphismTypeU B S hS
        (subspaceInclusion B S hS W W₀)) A' ≫ m) ≫
      pushforwardRingSheafCompHom B S hS e₀ (subspaceInclusion B S hS W W₀)
        (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z)))
      (((pushforwardRingFunctor (smallToposMorphismTypeU B S hS
        (subspaceInclusion B S hS W W₀))).map_comp _ _).symm)
  rw [key g, key g']
  erw [h]
  rfl

/-- **The carried-back solution agrees with the comorphism of `c` read through the thickening
after `r^♯`**, as soon as the two solutions on the site of `W₀` agree after `j^{-1}(r^♯)`.

This is the morphism-level form of the hypothesis of
`AlgebraicGeometry.Space.exists_thickeningLiftChartSiteHom_of_index`: the carried-back solution
and the comorphism of `c` read at the index `e₀ ≫ j` differ by a map annihilating the functions
read from `W'`. -/
theorem structureSharpRingInverseImage_comp_liftRestrictedSharpThroughThickening_eq
    (c : X ⟶ W)
    (e₀ : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS))
    (hc : subspaceInclusion B S hS X Z ≫ c = e₀ ≫ subspaceInclusion B S hS W W₀)
    {W' : AlgebraicSpaces B S hS} (r : W ⟶ W')
    (g : structureRingSheafInverseImage B S hS (subspaceInclusion B S hS W W₀) ⟶
      restrictedThickeningLiftRingSheaf B S hS Z W₀ e₀)
    (h : (inverseImageRingFunctor (smallToposMorphismTypeU B S hS
            (subspaceInclusion B S hS W W₀))).map
            (structureSharpRingInverseImage B S hS r) ≫ g =
        (inverseImageRingFunctor (smallToposMorphismTypeU B S hS
            (subspaceInclusion B S hS W W₀))).map
            (structureSharpRingInverseImage B S hS r) ≫
          restrictedSharpThroughThickening B S hS Z W₀ c e₀ hc) :
    structureSharpRingInverseImage B S hS r ≫
        liftRestrictedSharpThroughThickening B S hS Z W₀ e₀ g =
      structureSharpRingInverseImage B S hS r ≫
        structureSharpThroughThickeningAt B S hS Z c
          (e₀ ≫ subspaceInclusion B S hS W W₀) hc :=
  (comp_liftRestrictedSharpThroughThickening_congr B S hS Z W₀ e₀
      (structureSharpRingInverseImage B S hS r) g
      (restrictedSharpThroughThickening B S hS Z W₀ c e₀ hc) h).trans
    (congrArg (fun m ↦ structureSharpRingInverseImage B S hS r ≫ m)
      (liftRestrictedSharpThroughThickening_restrictedSharpThroughThickening
        B S hS Z W₀ c e₀ hc))

/-- **The hypothesis of
`AlgebraicGeometry.Space.exists_thickeningLiftChartSiteHom_of_index`, read on a section over an
étale chart.**  The two morphisms of sheaves of rings agree, so their values over any chart at
any value of `r^♯` agree. -/
theorem app_liftRestrictedSharpThroughThickening_eq
    (c : X ⟶ W)
    (e₀ : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS))
    (hc : subspaceInclusion B S hS X Z ≫ c = e₀ ≫ subspaceInclusion B S hS W W₀)
    {W' : AlgebraicSpaces B S hS} (r : W ⟶ W')
    (g : structureRingSheafInverseImage B S hS (subspaceInclusion B S hS W W₀) ⟶
      restrictedThickeningLiftRingSheaf B S hS Z W₀ e₀)
    (h : (inverseImageRingFunctor (smallToposMorphismTypeU B S hS
            (subspaceInclusion B S hS W W₀))).map
            (structureSharpRingInverseImage B S hS r) ≫ g =
        (inverseImageRingFunctor (smallToposMorphismTypeU B S hS
            (subspaceInclusion B S hS W W₀))).map
            (structureSharpRingInverseImage B S hS r) ≫
          restrictedSharpThroughThickening B S hS Z W₀ c e₀ hc)
    (V : (SmallEtale B S hS W.1)ᵒᵖ)
    (s : ToType ((structureRingSheafInverseImage B S hS r).obj.obj V)) :
    (liftRestrictedSharpThroughThickening B S hS Z W₀ e₀ g).hom.app V
        ((structureSharpRingInverseImage B S hS r).hom.app V s) =
      (structureSharpThroughThickeningAt B S hS Z c
          (e₀ ≫ subspaceInclusion B S hS W W₀) hc).hom.app V
        ((structureSharpRingInverseImage B S hS r).hom.app V s) :=
  (ringSheafHom_comp_app_apply (structureSharpRingInverseImage B S hS r)
        (liftRestrictedSharpThroughThickening B S hS Z W₀ e₀ g) V s).symm.trans
    ((ringSheafHom_congr_app_apply
          (structureSharpRingInverseImage_comp_liftRestrictedSharpThroughThickening_eq
            B S hS Z W₀ c e₀ hc r g h) V s).trans
      (ringSheafHom_comp_app_apply (structureSharpRingInverseImage B S hS r)
        (structureSharpThroughThickeningAt B S hS Z c
          (e₀ ≫ subspaceInclusion B S hS W W₀) hc) V s))

/-! ### The second member of the pair attached to a linear map -/

variable {Y T : AlgebraicSpaces B S hS} (b : Y ⟶ T)
  {A : Sheaf (SmallEtale.topology B S hS Y.1) RingCat.{u}}
  {q : A ⟶ structureRingSheaf B S hS Y}
  {X' : AlgebraicSpaces B S hS} (aa : X' ⟶ Y) (Cm : Modules B S hS X'.1 X'.2)
  {E : SquareZeroValues ((modulePushforward B S hS aa).obj Cm)}
  (f : A ⟶ E.ambient)
  (ι_smul : ∀ (V : (SmallEtale B S hS Y.1)ᵒᵖ) (x : A.obj.obj V)
    (m : ((modulePushforward B S hS aa).obj Cm).val.obj V),
    E.ι (@HSMul.hSMul
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O).obj.obj V)
      _ _ _ (q.hom.app V x) m) = f.hom.app V x * E.ι m)
  (θ : (modulePullback B S hS aa).obj (sheafOfDifferentials B S hS b) ⟶ Cm)

/-- **The second member of the pair of lifts attached to an `𝒪_X`-linear map agrees with the
first after a morphism whose values `q` carries into the kernel of the attached derivation.**

This is `Stacks.Sites.comp_derivationActionHom_eq` at the pair
`AlgebraicGeometry.Space.liftDifferenceDataOfHom`, so that a consumer never has to see the
underlying `Stacks.Sites.derivationActionHom`: the identification of the two is settled here,
in the abstract setting, rather than at the geometric terms where it is a deterministic
timeout. -/
theorem comp_liftDifferenceDataOfHom_g_eq {A' : Sheaf (SmallEtale.topology B S hS Y.1)
      RingCat.{u}} (ψ : A' ⟶ A)
    (hD : ∀ (V : (SmallEtale B S hS Y.1)ᵒᵖ) (x : A'.obj.obj V),
      derivationFamilyOfHom B S hS b aa Cm θ V (q.hom.app V (ψ.hom.app V x)) = 0) :
    ψ ≫ (liftDifferenceDataOfHom B S hS b aa Cm f ι_smul θ).g = ψ ≫ f :=
  comp_derivationActionHom_eq E f (derivationFamilyOfHom B S hS b aa Cm θ)
    (derivationFamilyOfHom_mul B S hS b aa Cm θ) (derivationFamilyOfHom_map B S hS b aa Cm θ)
    ι_smul ψ hD

end AlgebraicGeometry.Space

end
