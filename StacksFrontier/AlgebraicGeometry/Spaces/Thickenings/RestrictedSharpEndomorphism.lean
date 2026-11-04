module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ConormalInclusionRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftDifferenceSection
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ThickeningSharpLiftChartKernel

/-!
# The transported comorphism of a morphism followed by an endomorphism fixing a closed subspace

Let `Z ⊆ X` be a closed subspace of an algebraic space over a scheme `S`, with inclusion
`i : Z ⟶ X`, let `W₀ ⊆ W` be a closed subspace of a second algebraic space, with inclusion
`j : W₀ ⟶ W`, and let `c : X ⟶ W` be a morphism with `i ≫ c = e₀ ≫ j`.
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/LiftDifferenceRestrictedTarget.lean` transports
the comorphism of `c` to the small étale site of `W₀`, as a morphism of sheaves of rings

`j^{-1}𝒪_W ⟶ (e₀)_*(i^{-1}𝒪_X)`.

This file computes that transport for `c ≫ λ`, where `λ : W ⟶ W` is an endomorphism which is
the identity on `W₀`, that is `j ≫ λ = j`.  Such a `λ` induces a ring endomorphism `λ̃` of
`j^{-1}𝒪_W`, the adjunct along `j^{-1} ⊣ j_*` of the comorphism of `λ` read in
`(j ≫ λ)_*(j^{-1}𝒪_W) = j_*(j^{-1}𝒪_W)`, and

* the transport of `c ≫ λ` is `λ̃` followed by the transport of `c`
  (`AlgebraicGeometry.Space.restrictedSharpThroughThickening_comp_endomorphism`);
* `λ̃` is the identity after the reduction `j^♯ : j^{-1}𝒪_W ⟶ 𝒪_{W₀}`
  (`AlgebraicGeometry.Space.restrictedEndomorphismSharp_comp_structureSharpRingInverseImage`),
  because `λ` restricts to the identity of `W₀`.

Together they say that the difference of the transports of `c ≫ λ` and `c' ≫ λ` is the
difference of the transports of `c` and `c'` evaluated at `λ̃(x)` instead of `x`, and `λ̃(x) - x`
is killed by `j^♯`.  This is what makes the difference of two lifts invariant under such a `λ`,
which is the step of [Stacks Project, Tag 0CKF] where the composition of the groupoid of
sections is compared with the addition of the linear maps.

## Main definitions

* `AlgebraicGeometry.Space.restrictedEndomorphismSharp`: the ring endomorphism `λ̃` of
  `j^{-1}𝒪_W` induced by an endomorphism `λ` of `W` with `j ≫ λ = j`.

## Main results

* `AlgebraicGeometry.Space.pushforwardRingSheafCompHom_comp_inv_assoc`: the associativity
  cocycle of the comparisons of iterated direct images of sheaves of rings.
* `AlgebraicGeometry.Space.pushforwardRingSheafCompHom_comp_eqToHom_comp_inv`: the coherence of
  the comparisons of iterated direct images along `e₀`, `j` and `λ` when `j ≫ λ = j`.
* `AlgebraicGeometry.Space.restrictedEndomorphismSharp_comp_structureSharpRingInverseImage`:
  `λ̃ ≫ j^♯ = j^♯`.
* `AlgebraicGeometry.Space.restrictedSharpThroughThickening_comp_endomorphism`: the transport of
  the comorphism of `c ≫ λ` is `λ̃` followed by the transport of the comorphism of `c`.
* `Stacks.Sites.LiftDifferenceData.diff_comp_eq_of_comp_eq`: the difference of two lifts takes
  the same value at `ψ(x)` as at `x` when `ψ(x)` and `x` have the same image under `q`.

## Implementation notes

As in `StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/LiftDifferenceSection.lean`, every
manipulation of the large composites is done by a lemma stated over an abstract category, with
every morphism a variable, and then instantiated; rewriting with `Category.assoc` directly on
the geometric terms does not terminate in reasonable time.  The coherence of the comparisons of
iterated direct images is proved on underlying sheaves of sets, where it is the associativity
cocycle `AlgebraicGeometry.Space.smallToposMorphismTypeU_comp_assoc` of
[Stacks Project, Tag 03G2], part (3), together with the transport along `j ≫ λ = j`.

## References

* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2), part (3).
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8).
* [Stacks Project, Tag 0618](https://stacks.math.columbia.edu/tag/0618).
* [Stacks Project, Tag 0CKF](https://stacks.math.columbia.edu/tag/0CKF).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace Stacks.Sites.LiftDifferenceData

universe v₀ u₀

variable {Cs : Type u₀} [Category.{v₀} Cs] {J : GrothendieckTopology Cs}
  {A O : Sheaf J RingCat.{u}} {q : A ⟶ O} {M : SheafOfModules.{u} O} {E : SquareZeroValues M}

/-- **The difference of two lifts is unchanged by an endomorphism of the source which is the
identity after `q`.**  If `ψ(x)` and `x` have the same image under `q`, then `ψ(x) - x` is
killed by `q`, where the two lifts agree, so their difference at `ψ(x)` is their difference at
`x`. -/
theorem diff_comp_eq_of_comp_eq (L : LiftDifferenceData q E) (ψ : A ⟶ A) {V : Csᵒᵖ}
    (x : A.obj.obj V) (hx : q.hom.app V (ψ.hom.app V x) = q.hom.app V x) :
    L.diff (ψ.hom.app V x) = L.diff x := by
  have hzero : L.diff (ψ.hom.app V x - x) = 0 :=
    L.diff_eq_zero_of_app_eq_zero _ (by rw [map_sub, hx, sub_self])
  have hsum := L.diff_add x (ψ.hom.app V x - x)
  rw [add_sub_cancel, hzero, add_zero] at hsum
  exact hsum

end Stacks.Sites.LiftDifferenceData

namespace AlgebraicGeometry.Space

/-! ### Abstract bookkeeping -/

section Abstract

universe v₁ u₁

variable {Cc : Type u₁} [Category.{v₁} Cc]

/-- An associativity cocycle read with two of its four comparisons inverted, with every
morphism a variable. -/
private theorem cocycle_inv {C₂ : Type*} [Category C₂] (F : Cc ⥤ C₂) {X Y : Cc}
    {Z W : C₂} (a : X ⟶ Y) (ai : Y ⟶ X) (hai : ai ≫ a = 𝟙 Y) (b : F.obj Y ⟶ Z)
    (c : F.obj X ⟶ W) (d : W ⟶ Z) (dinv : Z ⟶ W) (hd : d ≫ dinv = 𝟙 W)
    (h : F.map a ≫ b = c ≫ d) : b ≫ dinv = F.map ai ≫ c := by
  have hb : b = F.map ai ≫ c ≫ d := by
    rw [← h, ← F.map_comp_assoc, hai, F.map_id, Category.id_comp]
  rw [hb, Category.assoc, Category.assoc, hd, Category.comp_id]

/-- The chase behind `restrictedSharpThroughThickening_comp_endomorphism`, with every morphism
a variable. -/
private theorem endomorphism_chase {O FO JJ FJJ JE FJE K FK JLJ JLE KL : Cc}
    (P : O ⟶ FO) (Fu : FO ⟶ FJJ) (jres : JJ ⟶ JE) (Fj : FJJ ⟶ FJE) (Fs : FO ⟶ FK)
    (cinv : K ⟶ JE) (Fc : FK ⟶ FJE)
    (chJ : FJJ ⟶ JLJ) (eJ : JLJ ⟶ JJ) (jlres : JLJ ⟶ JLE) (chE : FJE ⟶ JLE)
    (eE : JLE ⟶ JE) (chK : FK ⟶ KL) (eK : KL ⟶ K) (scl : O ⟶ KL)
    (hadj : Fu ≫ Fj = Fs ≫ Fc) (hslide : eJ ≫ jres = jlres ≫ eE)
    (hnat : Fj ≫ chE = chJ ≫ jlres) (hfunc : (P ≫ Fs) ≫ chK = scl)
    (hcoh : chK ≫ eK ≫ cinv = Fc ≫ chE ≫ eE) :
    (scl ≫ eK) ≫ cinv = ((P ≫ Fu ≫ chJ) ≫ eJ) ≫ jres := by
  rw [← hfunc]
  simp only [Category.assoc]
  rw [hslide, ← reassoc_of% hnat, reassoc_of% hadj, hcoh]

end Abstract

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The comparison of iterated direct images -/

section PushforwardComp

variable {V₀ V₁ V₂ : AlgebraicSpaces B S hS}

/-- **The associativity cocycle of the comparisons of iterated direct images of sheaves of
rings**, along `e₀`, `j` and `l`: from `l_*((e₀ ≫ j)_*N)` to `(j ≫ l)_*((e₀)_*N)`, through
`(e₀ ≫ j ≫ l)_*N` or through `l_*(j_*((e₀)_*N))`.  On underlying sheaves of sets it is
`AlgebraicGeometry.Space.smallToposMorphismTypeU_comp_assoc`. -/
theorem pushforwardRingSheafCompHom_comp_inv_assoc (e₀ : V₀ ⟶ V₁) (j : V₁ ⟶ V₂)
    {V₃ : AlgebraicSpaces B S hS} (l : V₂ ⟶ V₃)
    (N : Sheaf (SmallEtale.topology B S hS V₀.1) RingCat.{u}) :
    pushforwardRingSheafCompHom B S hS (e₀ ≫ j) l N ≫
        pushforwardRingSheafCompInv B S hS e₀ (j ≫ l) N =
      pullbackRingSheafMap (SmallEtale.topology B S hS V₃.1)
          (smallToposMorphismTypeU B S hS l).pushforward
          (pushforwardRingSheafCompInv B S hS e₀ j N) ≫
        pushforwardRingSheafCompHom B S hS j l
          (pullbackRingSheaf.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS V₁.1)
            (smallToposMorphismTypeU B S hS e₀).pushforward N) := by
  refine (sheafCompose (SmallEtale.topology B S hS V₃.1)
    (CategoryTheory.forget RingCat.{u})).map_injective ?_
  let N' := (sheafCompose (SmallEtale.topology B S hS V₀.1)
    (CategoryTheory.forget RingCat.{u})).obj N
  have hset := cocycle_inv (smallToposMorphismTypeU B S hS l).pushforward
    ((smallToposMorphismTypeU_comp B S hS e₀ j).hom.app N')
    ((smallToposMorphismTypeU_comp B S hS e₀ j).inv.app N')
    ((smallToposMorphismTypeU_comp B S hS e₀ j).inv_hom_id_app N')
    ((smallToposMorphismTypeU_comp B S hS (e₀ ≫ j) l).hom.app N')
    ((smallToposMorphismTypeU_comp B S hS j l).hom.app
      ((smallToposMorphismTypeU B S hS e₀).pushforward.obj N'))
    ((smallToposMorphismTypeU_comp B S hS e₀ (j ≫ l)).hom.app N')
    ((smallToposMorphismTypeU_comp B S hS e₀ (j ≫ l)).inv.app N')
    ((smallToposMorphismTypeU_comp B S hS e₀ (j ≫ l)).hom_inv_id_app N')
    (smallToposMorphismTypeU_comp_assoc B S hS e₀ j l N')
  rw [Functor.map_comp, Functor.map_comp, sheafCompose_map_pushforwardRingSheafCompHom,
    sheafCompose_map_pushforwardRingSheafCompHom, sheafCompose_map_pushforwardRingSheafCompInv,
    ringSheafMap_pullbackRingSheafMap,
    sheafCompose_map_pushforwardRingSheafCompInv]
  exact hset

/-- A square with a transport along a reflexive equation inserted on either side. -/
private theorem comp_eqToHom_comp_of_comp {Cc : Type*} [Category Cc] {X Y Z W : Cc}
    (a : X ⟶ Y) (b : Y ⟶ Z) (c : X ⟶ W) (d : W ⟶ Z) (p : Y = Y) (q : Z = Z)
    (h : a ≫ b = c ≫ d) : a ≫ eqToHom p ≫ b = c ≫ d ≫ eqToHom q := by
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id, h]

/-- **The coherence of the comparisons of iterated direct images along `e₀`, `j` and a morphism
`l` with `j ≫ l = j'`.**  Going from `l_*((e₀ ≫ j)_*N)` to `j'_*((e₀)_*N)` through
`((e₀ ≫ j) ≫ l)_*N = (e₀ ≫ j')_*N` agrees with going through `l_*(j_*((e₀)_*N))` and
`(j ≫ l)_*((e₀)_*N) = j'_*((e₀)_*N)`. -/
theorem pushforwardRingSheafCompHom_comp_eqToHom_comp_inv (e₀ : V₀ ⟶ V₁) (j j' : V₁ ⟶ V₂)
    (l : V₂ ⟶ V₂) (hl : j ≫ l = j')
    (N : Sheaf (SmallEtale.topology B S hS V₀.1) RingCat.{u}) :
    pushforwardRingSheafCompHom B S hS (e₀ ≫ j) l N ≫
        eqToHom (congrArg (fun m : V₀ ⟶ V₂ ↦
          pullbackRingSheaf.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS V₂.1)
            (smallToposMorphismTypeU B S hS m).pushforward N)
          ((Category.assoc e₀ j l).trans (congrArg (e₀ ≫ ·) hl))) ≫
        pushforwardRingSheafCompInv B S hS e₀ j' N =
      (pushforwardRingFunctor (smallToposMorphismTypeU B S hS l)).map
          (pushforwardRingSheafCompInv B S hS e₀ j N) ≫
        pushforwardRingSheafCompHom B S hS j l
          (pullbackRingSheaf.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS V₁.1)
            (smallToposMorphismTypeU B S hS e₀).pushforward N) ≫
        eqToHom (congrArg (fun m : V₁ ⟶ V₂ ↦
          pullbackRingSheaf.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS V₂.1)
            (smallToposMorphismTypeU B S hS m).pushforward
            (pullbackRingSheaf.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS V₁.1)
              (smallToposMorphismTypeU B S hS e₀).pushforward N)) hl) := by
  subst hl
  exact comp_eqToHom_comp_of_comp _ _ _ _ _ _
    (pushforwardRingSheafCompHom_comp_inv_assoc B S hS e₀ j l N)

end PushforwardComp

/-! ### The endomorphism of `j^{-1}𝒪_W` induced by an endomorphism fixing `W₀` -/

section Endomorphism

variable {W : AlgebraicSpaces B S hS} (W₀ : ClosedSubspaces B S hS W.1)

/-- **The ring endomorphism `λ̃` of `j^{-1}𝒪_W` induced by an endomorphism `λ` of `W` which is
the identity on the closed subspace `W₀`**, `j ≫ λ = j`: the adjunct along `j^{-1} ⊣ j_*` of the
comorphism of `λ` read in `(j ≫ λ)_*(j^{-1}𝒪_W) = j_*(j^{-1}𝒪_W)`, which is
`AlgebraicGeometry.Space.structureSharpThroughThickeningAt` for the closed subspace `W₀ ⊆ W`. -/
noncomputable def restrictedEndomorphismSharp (l : W ⟶ W)
    (hl : subspaceInclusion B S hS W W₀ ≫ l = subspaceInclusion B S hS W W₀) :
    structureRingSheafInverseImage B S hS (subspaceInclusion B S hS W W₀) ⟶
      structureRingSheafInverseImage B S hS (subspaceInclusion B S hS W W₀) :=
  ((ringImageAdjunction (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS W W₀))).homEquiv
      (structureRingSheaf B S hS W)
      (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS W W₀))).symm
    (structureSharpThroughThickeningAt B S hS W₀ l (subspaceInclusion B S hS W W₀) hl)

/-- **`λ̃` is the identity after the reduction `j^♯ : j^{-1}𝒪_W ⟶ 𝒪_{W₀}`.**  Its adjunct
followed by the direct image of `j^♯` is the comorphism of `j ≫ λ = j`, by
`AlgebraicGeometry.Space.structureSharpThroughThickeningAt_comp_reduction`, and that is the
adjunct of `j^♯`. -/
theorem restrictedEndomorphismSharp_comp_structureSharpRingInverseImage (l : W ⟶ W)
    (hl : subspaceInclusion B S hS W W₀ ≫ l = subspaceInclusion B S hS W W₀) :
    restrictedEndomorphismSharp B S hS W₀ l hl ≫
        structureSharpRingInverseImage B S hS (subspaceInclusion B S hS W W₀) =
      structureSharpRingInverseImage B S hS (subspaceInclusion B S hS W W₀) :=
  (Adjunction.homEquiv_naturality_right_symm (ringImageAdjunction
      (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS W W₀))) _ _).symm.trans
    (congrArg ((ringImageAdjunction (smallToposMorphismTypeU B S hS
      (subspaceInclusion B S hS W W₀))).homEquiv (structureRingSheaf B S hS W)
      (structureRingSheaf B S hS (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS))).symm
      (structureSharpThroughThickeningAt_comp_reduction B S hS W₀ l
        (subspaceInclusion B S hS W W₀) hl))

/-- The comorphism read in the direct image along one of two equal morphisms is the comorphism
read in the direct image along the other, transported. -/
private theorem structureSharpThroughThickeningAt_eq_comp_eqToHom {X : AlgebraicSpaces B S hS}
    (Z : ClosedSubspaces B S hS X.1) (c : X ⟶ W)
    (e e' : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ W)
    (h : subspaceInclusion B S hS X Z ≫ c = e) (h' : subspaceInclusion B S hS X Z ≫ c = e')
    (he : e = e') :
    structureSharpThroughThickeningAt B S hS Z c e' h' =
      structureSharpThroughThickeningAt B S hS Z c e h ≫
        eqToHom (congrArg (fun m : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ W ↦
          pullbackRingSheaf.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS W.1)
            (smallToposMorphismTypeU B S hS m).pushforward
            (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z))) he) := by
  subst he
  simp

/-- Transport along an equality of morphisms commutes with the direct image of a morphism of
sheaves of rings. -/
private theorem eqToHom_comp_map_pushforward {V : AlgebraicSpaces B S hS}
    {O O' : Sheaf (SmallEtale.topology B S hS V.1) RingCat.{u}} (a : O ⟶ O') (m m' : V ⟶ W)
    (hm : m = m') :
    eqToHom (congrArg (fun k : V ⟶ W ↦
        pullbackRingSheaf.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS W.1)
          (smallToposMorphismTypeU B S hS k).pushforward O) hm) ≫
        (pushforwardRingFunctor (smallToposMorphismTypeU B S hS m')).map a =
      (pushforwardRingFunctor (smallToposMorphismTypeU B S hS m)).map a ≫
        eqToHom (congrArg (fun k : V ⟶ W ↦
          pullbackRingSheaf.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS W.1)
            (smallToposMorphismTypeU B S hS k).pushforward O') hm) := by
  subst hm
  simp

variable {X : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)

/-- **The comorphism of `c : X ⟶ W` read through the thickening and then along any morphism
`g : W ⟶ V` is the comorphism of `c ≫ g` read through the thickening**, through the comparison of
iterated direct images, with the restriction to the thickening named.  This is
`AlgebraicGeometry.Space.structureSharpThroughThickening_comp` in the form of
`AlgebraicGeometry.Space.structureSharp_comp_map_structureSharpThroughThickeningAt`, which states
it for a morphism back to `X` only. -/
theorem structureSharpThroughThickeningAt_comp {V : AlgebraicSpaces B S hS} (c : X ⟶ W)
    (g : W ⟶ V) (κ : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ W)
    (h : subspaceInclusion B S hS X Z ≫ c = κ) :
    (structureSharp B S hS g ≫
        (pushforwardRingFunctor (smallToposMorphismTypeU B S hS g)).map
          (structureSharpThroughThickeningAt B S hS Z c κ h)) ≫
        pushforwardRingSheafCompHom B S hS κ g
          (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z)) =
      structureSharpThroughThickeningAt B S hS Z (c ≫ g) (κ ≫ g)
        ((Category.assoc _ _ _).symm.trans (congrArg (fun m => m ≫ g) h)) := by
  cases h
  have e : ∀ {V : AlgebraicSpaces B S hS} (c' : X ⟶ V)
      (hk : subspaceInclusion B S hS X Z ≫ c' = subspaceInclusion B S hS X Z ≫ c'),
      structureSharpThroughThickeningAt B S hS Z c' _ hk =
        structureSharpThroughThickening B S hS Z c' := fun _ _ => Category.comp_id _
  rw [e c]
  exact (Category.assoc _ _ _).trans
    ((structureSharpThroughThickening_comp B S hS Z c g).trans (e (c ≫ g) _).symm)

/-- **The transported comorphism of `c ≫ λ`, for an endomorphism `λ` of `W` which is the
identity on `W₀`, is `λ̃` followed by the transported comorphism of `c`.**

Both sides are adjuncts along `j^{-1} ⊣ j_*`.  The adjunct of the right hand side is the
comorphism of `λ` read in `j_*(j^{-1}𝒪_W)` followed by the direct image of the transport of
`c`; the adjunction identity of the transport of `c`
(`AlgebraicGeometry.Space.ringUnit_comp_map_restrictedSharpThroughThickening`), the naturality
of the comparison of iterated direct images, the functoriality of the comorphism read through
the thickening (`AlgebraicGeometry.Space.structureSharpThroughThickeningAt_comp`)
and the coherence `AlgebraicGeometry.Space.pushforwardRingSheafCompHom_comp_eqToHom_comp_inv`
turn it into the adjunct of the left hand side. -/
theorem restrictedSharpThroughThickening_comp_endomorphism (c : X ⟶ W)
    (e₀ : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS))
    (h : subspaceInclusion B S hS X Z ≫ c = e₀ ≫ subspaceInclusion B S hS W W₀)
    (l : W ⟶ W) (hl : subspaceInclusion B S hS W W₀ ≫ l = subspaceInclusion B S hS W W₀)
    (h' : subspaceInclusion B S hS X Z ≫ c ≫ l = e₀ ≫ subspaceInclusion B S hS W W₀) :
    restrictedSharpThroughThickening B S hS Z W₀ (c ≫ l) e₀ h' =
      restrictedEndomorphismSharp B S hS W₀ l hl ≫
        restrictedSharpThroughThickening B S hS Z W₀ c e₀ h := by
  have hκ : (e₀ ≫ subspaceInclusion B S hS W W₀) ≫ l = e₀ ≫ subspaceInclusion B S hS W W₀ :=
    (Category.assoc _ _ _).trans (congrArg (e₀ ≫ ·) hl)
  have hcl : subspaceInclusion B S hS X Z ≫ c ≫ l =
      (e₀ ≫ subspaceInclusion B S hS W W₀) ≫ l :=
    (Category.assoc _ _ _).symm.trans (congrArg (fun m ↦ m ≫ l) h)
  have hadj := ringUnit_comp_map_restrictedSharpThroughThickening B S hS Z W₀ c e₀ h
  have hFadj :=
    ((pushforwardRingFunctor (smallToposMorphismTypeU B S hS l)).map_comp _ _).symm.trans
    ((congrArg (pushforwardRingFunctor (smallToposMorphismTypeU B S hS l)).map hadj).trans
      ((pushforwardRingFunctor (smallToposMorphismTypeU B S hS l)).map_comp _ _))
  have hslide := eqToHom_comp_map_pushforward B S hS
    (restrictedSharpThroughThickening B S hS Z W₀ c e₀ h)
    (subspaceInclusion B S hS W W₀ ≫ l) (subspaceInclusion B S hS W W₀) hl
  have hnat := pushforwardRingSheafCompHom_naturality B S hS (subspaceInclusion B S hS W W₀) l
    (restrictedSharpThroughThickening B S hS Z W₀ c e₀ h)
  have hfunc := structureSharpThroughThickeningAt_comp B S hS Z c l
    (e₀ ≫ subspaceInclusion B S hS W W₀) h
  have hcoh := pushforwardRingSheafCompHom_comp_eqToHom_comp_inv B S hS e₀
    (subspaceInclusion B S hS W W₀) (subspaceInclusion B S hS W W₀) l hl
    (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z))
  have hmain := endomorphism_chase _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hFadj hslide hnat hfunc hcoh
  rw [← structureSharpThroughThickeningAt_eq_comp_eqToHom B S hS Z (c ≫ l) _ _ hcl h' hκ]
    at hmain
  refine (congrArg ((ringImageAdjunction (smallToposMorphismTypeU B S hS
      (subspaceInclusion B S hS W W₀))).homEquiv (structureRingSheaf B S hS W)
      (restrictedThickeningLiftRingSheaf B S hS Z W₀ e₀)).symm hmain).trans ?_
  exact Adjunction.homEquiv_naturality_right_symm _ _ _

end Endomorphism

end AlgebraicGeometry.Space

end
