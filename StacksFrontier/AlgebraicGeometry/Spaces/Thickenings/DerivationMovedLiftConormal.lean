module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ConormalMapAgreement
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.DerivationMovedLift
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftDifferenceBaseAgreementOver

/-!
# Infinitesimal deformations of a morphism of first order thickenings

Let `Z ⊂ X` and `W₀ ⊂ W` be first order thickenings of algebraic spaces over a base algebraic
space `T` (structure morphisms `p : X ⟶ T` and `q : W ⟶ T`), with inclusions `i` and `j`, and let
`(e₀, c) : (Z ⊂ X) ⟶ (W₀ ⊂ W)` be a morphism of thickenings over `T`.  For an `𝒪_Z`-linear map
`θ : e₀^*Ω_{W₀/T} ⟶ 𝒞_{Z/X}` this file proves [Stacks Project, Tag 04D0]: there is exactly one
morphism of thickenings `(e₀, b') : (Z ⊂ X) ⟶ (W₀ ⊂ W)` over `T` such that

1. its reduction is `e₀`, the reduction of `(e₀, c)`;
2. the two maps `e₀^*𝒞_{W₀/W} ⟶ 𝒞_{Z/X}` of [Stacks Project, Tag 04CP] induced by `c` and by
   `b'` are equal; and
3. `c^♯ − (b')^♯ = ι ∘ D ∘ j^♯`, where `D = d_{W₀/T} ∘ θ` is the `𝒪_T`-derivation attached to `θ`
   by Equation [Stacks Project, Tag 0619].

As in the source, the comorphisms are read as maps of sheaves on the small étale site of `W₀`:
`c^♯, (b')^♯ : j^{-1}𝒪_W ⟶ (e₀)_*(i^{-1}𝒪_X)`, the difference taking its values in the ideal
`(e₀)_*𝒞_{Z/X}`.

The existence and uniqueness with condition 2 read on the defining ideal,
`AlgebraicGeometry.Space.existsUnique_hom_agreeOnIdeal_derivation_eq`, is translated into the
form of the source by the bridge of
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/ConormalMapAgreement.lean`.

Conversely ([Stacks Project, Tag 0618]): two morphisms of thickenings `(e₀, c), (e₀, c')` over
`T` with the same map of conormal modules differ by an `𝒪_T`-derivation
`D : 𝒪_{W₀} ⟶ (e₀)_*𝒞_{Z/X}`, in the sense that `c^♯ − (c')^♯ = ι ∘ D ∘ j^♯`.  The difference of
the two transported comorphisms agrees on the kernel of `j^♯` by the bridge, so it descends along
the locally surjective `j^♯` to a derivation of `𝒪_{W₀}`
(`AlgebraicGeometry.Space.descendedDerivation`); it kills the functions read from `T` because
both morphisms are over `T`.

## Main results

* `AlgebraicGeometry.Space.existsUnique_hom_conormalMap_eq_derivation_eq`:
  [Stacks Project, Tag 04D0].
* `AlgebraicGeometry.Space.derivationMove_spec`: [Stacks Project, Tag 0CK6], the action
  `θ · c := AlgebraicGeometry.Space.derivationMove` and what it means.
* `AlgebraicGeometry.Space.exists_derivation_of_conormalMap_eq`: [Stacks Project, Tag 0618].

## References

* [Stacks Project, Tag 04D0](https://stacks.math.columbia.edu/tag/04D0)
* [Stacks Project, Tag 0618](https://stacks.math.columbia.edu/tag/0618)
* [Stacks Project, Tag 0619](https://stacks.math.columbia.edu/tag/0619)
* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP)
* [Stacks Project, Tag 0CK6](https://stacks.math.columbia.edu/tag/0CK6)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X W T : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)
  (W₀ : ClosedSubspaces B S hS W.1)
  (e₀ : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
    (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS))
  (q : W ⟶ T)
  (hZ : IsFirstOrderThickening B S hS X Z.1) (hW : IsFirstOrderThickening B S hS W W₀.1)
  (c : X ⟶ W) (hc : subspaceInclusion B S hS X Z ≫ c = e₀ ≫ subspaceInclusion B S hS W W₀)

include hW in
/-- **[Stacks Project, Tag 04D0].**  Let `(e₀, c) : (Z ⊂ X) ⟶ (W₀ ⊂ W)` be a morphism of first
order thickenings over `T` (`i ≫ c = e₀ ≫ j` and `c ≫ q = p`), and let
`θ : e₀^*Ω_{W₀/T} ⟶ 𝒞_{Z/X}` be `𝒪_Z`-linear.  Then there is exactly one morphism `b' : X ⟶ W`
such that `(e₀, b')` is a morphism of thickenings over `T` (`i ≫ b' = e₀ ≫ j` and `b' ≫ q = p`:
condition (1) of [Stacks Project, Tag 0618], `b = a`), the two maps `e₀^*𝒞_{W₀/W} ⟶ 𝒞_{Z/X}` of
[Stacks Project, Tag 04CP] are equal (condition (2)), and the comorphisms, read as maps
`j^{-1}𝒪_W ⟶ (e₀)_*(i^{-1}𝒪_X)`, differ by `ι ∘ D ∘ j^♯` with `D = d_{W₀/T} ∘ θ` the derivation of
Equation [Stacks Project, Tag 0619]. -/
@[stacks 04D0 "the morphism of pairs (b, b') = (a, b') moved by θ: conditions (1) and (2) of \
0618, with the derivation D of 0618 equal to d_{Y/B} ∘ θ (Equation 0619)"]
theorem existsUnique_hom_conormalMap_eq_derivation_eq
    (θ : (modulePullback B S hS e₀).obj
        (sheafOfDifferentials B S hS (subspaceInclusion B S hS W W₀ ≫ q)) ⟶
      conormalModule B S hS X Z)
    (p : X ⟶ T) (hcq : c ≫ q = p) :
    ∃! b' : X ⟶ W, ∃ (hb : subspaceInclusion B S hS X Z ≫ b' =
        e₀ ≫ subspaceInclusion B S hS W W₀),
      b' ≫ q = p ∧
        conormalMap B S hS Z W₀ c e₀ hc = conormalMap B S hS Z W₀ b' e₀ hb ∧
        ∀ (V : (SmallEtale B S hS (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
          (x : ToType ((structureRingSheafInverseImage B S hS
            (subspaceInclusion B S hS W W₀)).obj.obj V)),
          (restrictedSquareZeroValues B S hS Z W₀ e₀ hZ).ι
              (derivationFamilyOfHom B S hS (subspaceInclusion B S hS W W₀ ≫ q) e₀
                (conormalModule B S hS X Z) θ V
                ((structureSharpRingInverseImage B S hS
                  (subspaceInclusion B S hS W W₀)).hom.app V x)) =
            (restrictedSharpThroughThickening B S hS Z W₀ c e₀ hc).hom.app V x -
              (restrictedSharpThroughThickening B S hS Z W₀ b' e₀ hb).hom.app V x := by
  obtain ⟨b', ⟨hb, hbq, hag, hD⟩, -⟩ :=
    existsUnique_hom_agreeOnIdeal_derivation_eq B S hS Z W₀ e₀ q hZ c hc θ p hcq
  refine ⟨b', ⟨hb, hbq, ?_, hD⟩, ?_⟩
  · exact (conormalMap_eq_conormalMap_iff_at B S hS Z W₀ c e₀
        (comp_eq_comp_algebraicSpaces B S hS Z W₀ e₀ c hc) hZ b'
        (comp_eq_comp_algebraicSpaces B S hS Z W₀ e₀ b' hb) _ hc hb).2
      (structureSharpThroughThickeningAt_ι_eq_of_restrictedSharpThroughThickening_eq B S hS Z W₀
        e₀ hW c b' hc hb fun V x hx ↦ (hag V x hx).symm)
  · rintro b'' ⟨hb'', -, -, hD''⟩
    exact eq_of_ι_derivationFamilyOfHom_eq_sub B S hS Z W₀ e₀ q hZ c hc θ b'' b' hb'' hb
      (fun {V x} ↦ hD'' V x) (fun {V x} ↦ hD V x)

/-- **The action `θ · c` of [Stacks Project, Tag 0CK6]**: the morphism `b' : X ⟶ W` that
[Stacks Project, Tag 04D0] attaches to `θ` and the morphism of thickenings `(e₀, c)` over `T`,
the one whose transported comorphism is `c^♯ − ι ∘ D ∘ j^♯`. -/
noncomputable abbrev derivationMove
    (θ : (modulePullback B S hS e₀).obj
        (sheafOfDifferentials B S hS (subspaceInclusion B S hS W W₀ ≫ q)) ⟶
      conormalModule B S hS X Z)
    (p : X ⟶ T) (hcq : c ≫ q = p) : X ⟶ W :=
  Classical.choose (exists_hom_restrictedSharpThroughThickening_eq_movedLiftData_g B S hS Z W₀ e₀ q
    hZ c hc θ p hcq)

include hW in
/-- **[Stacks Project, Tag 0CK6].**  The action `θ · c` of a local section `θ` of
`SheafHom(e₀^*Ω_{W₀/T}, 𝒞_{Z/X})` on `c` means nothing else than this: `(e₀, θ · c)` is a
morphism of thickenings over `T` with the same map of conormal modules as `(e₀, c)`, and `c^♯`
and `(θ · c)^♯` differ by the derivation `D = d_{W₀/T} ∘ θ` of Equation
[Stacks Project, Tag 0619], read as maps `j^{-1}𝒪_W ⟶ (e₀)_*(i^{-1}𝒪_X)`. -/
@[stacks 0CK6 "the action θ · a' of a local section θ: (a')^♯ and (θ · a')^♯ differ by the \
derivation D related to θ by Equation 0619"]
theorem derivationMove_spec
    (θ : (modulePullback B S hS e₀).obj
        (sheafOfDifferentials B S hS (subspaceInclusion B S hS W W₀ ≫ q)) ⟶
      conormalModule B S hS X Z)
    (p : X ⟶ T) (hcq : c ≫ q = p) :
    ∃ (hb : subspaceInclusion B S hS X Z ≫ derivationMove B S hS Z W₀ e₀ q hZ c hc θ p hcq =
        e₀ ≫ subspaceInclusion B S hS W W₀),
      derivationMove B S hS Z W₀ e₀ q hZ c hc θ p hcq ≫ q = p ∧
        conormalMap B S hS Z W₀ c e₀ hc =
          conormalMap B S hS Z W₀ (derivationMove B S hS Z W₀ e₀ q hZ c hc θ p hcq) e₀ hb ∧
        ∀ (V : (SmallEtale B S hS (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
          (x : ToType ((structureRingSheafInverseImage B S hS (subspaceInclusion B S hS W
              W₀)).obj.obj V)),
          (restrictedSquareZeroValues B S hS Z W₀ e₀ hZ).ι
              (derivationFamilyOfHom B S hS (subspaceInclusion B S hS W W₀ ≫ q) e₀
                (conormalModule B S hS X Z) θ V
                ((structureSharpRingInverseImage B S hS (subspaceInclusion B S hS W W₀)).hom.app V
                    x)) =
            (restrictedSharpThroughThickening B S hS Z W₀ c e₀ hc).hom.app V x -
              (restrictedSharpThroughThickening B S hS Z W₀
                (derivationMove B S hS Z W₀ e₀ q hZ c hc θ p hcq) e₀ hb).hom.app V x :=
  by
  obtain ⟨hb, hbq, hbg⟩ := Classical.choose_spec
    (exists_hom_restrictedSharpThroughThickening_eq_movedLiftData_g B S hS Z W₀ e₀ q hZ c hc θ p
      hcq)
  refine ⟨hb, hbq, ?_, fun V x ↦ (agree_and_ι_derivationFamilyOfHom_of_eq_movedLiftData_g B S hS Z
    W₀ e₀ q hZ c hc θ _ hb hbg (V := V) (x := x)).2⟩
  exact (conormalMap_eq_conormalMap_iff_at B S hS Z W₀ c e₀
      (comp_eq_comp_algebraicSpaces B S hS Z W₀ e₀ c hc) hZ _
      (comp_eq_comp_algebraicSpaces B S hS Z W₀ e₀ _ hb) _ hc hb).2
    (structureSharpThroughThickeningAt_ι_eq_of_restrictedSharpThroughThickening_eq B S hS Z W₀ e₀
      hW c _ hc hb fun V x hx ↦
        ((agree_and_ι_derivationFamilyOfHom_of_eq_movedLiftData_g B S hS Z W₀ e₀ q hZ c hc θ _ hb
          hbg (V := V) (x := x)).1 hx).symm)

include hW in
/-- The action `θ · c` is the only morphism with the properties of
`AlgebraicGeometry.Space.derivationMove_spec`. -/
theorem eq_derivationMove
    (θ : (modulePullback B S hS e₀).obj
        (sheafOfDifferentials B S hS (subspaceInclusion B S hS W W₀ ≫ q)) ⟶
      conormalModule B S hS X Z)
    (p : X ⟶ T) (hcq : c ≫ q = p) (b' : X ⟶ W)
    (hb' : ∃ (hb : subspaceInclusion B S hS X Z ≫ b' = e₀ ≫ subspaceInclusion B S hS W W₀),
      b' ≫ q = p ∧
        conormalMap B S hS Z W₀ c e₀ hc = conormalMap B S hS Z W₀ b' e₀ hb ∧
        ∀ (V : (SmallEtale B S hS (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
          (x : ToType ((structureRingSheafInverseImage B S hS (subspaceInclusion B S hS W
              W₀)).obj.obj V)),
          (restrictedSquareZeroValues B S hS Z W₀ e₀ hZ).ι
              (derivationFamilyOfHom B S hS (subspaceInclusion B S hS W W₀ ≫ q) e₀
                (conormalModule B S hS X Z) θ V
                ((structureSharpRingInverseImage B S hS (subspaceInclusion B S hS W W₀)).hom.app V
                    x)) =
            (restrictedSharpThroughThickening B S hS Z W₀ c e₀ hc).hom.app V x -
              (restrictedSharpThroughThickening B S hS Z W₀ b' e₀ hb).hom.app V x) :
    b' = derivationMove B S hS Z W₀ e₀ q hZ c hc θ p hcq := by
  obtain ⟨hb, -, -, hD⟩ := hb'
  obtain ⟨hb₂, -, -, hD₂⟩ := derivationMove_spec B S hS Z W₀ e₀ q hZ hW c hc θ p hcq
  exact eq_of_ι_derivationFamilyOfHom_eq_sub B S hS Z W₀ e₀ q hZ c hc θ b' _ hb hb₂
    (fun {V x} ↦ hD V x) (fun {V x} ↦ hD₂ V x)

/-- The function read from `T` along `j ≫ q` is the image under `j^♯` of the function read from
`T` along `q`, through the composition law `(j ≫ q)^{-1} ≅ j^{-1}q^{-1}` of
[Stacks Project, Tag 03G8].  This is the computation inside
`AlgebraicGeometry.Space.derivationFamilyOfHom_app_base_eq_zero`, at an arbitrary section. -/
theorem structureSharpRingInverseImage_app_inverseImage_eq
    (V : (SmallEtale B S hS (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
    (x : ToType (((smallEtaleInverseImageRing B S hS (subspaceInclusion B S hS W W₀)).obj
      (inverseImageStructureSheaf B S hS q)).obj.obj V)) :
    (structureSharpRingInverseImage B S hS (subspaceInclusion B S hS W W₀)).hom.app V
        (((inverseImageRingFunctor (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS W
            W₀))).map
            (structureSharpRingInverseImage B S hS q)).hom.app V x) =
      (structureSharpInverseImage B S hS (subspaceInclusion B S hS W W₀ ≫ q)).hom.app V
        (((smallEtaleRingedToposHom_compInverseImageRingIso B S hS (subspaceInclusion B S hS W W₀)
            q).hom.app
            (smallEtaleRingedTopos B S hS T).O).hom.app V x) := by
  have hcomp := ConcreteCategory.congr_hom (NatTrans.congr_app (congrArg (fun m => m.hom)
    (smallEtaleRingedToposHom_compInverseImageRingIso_fSharpInverseImage B S hS (subspaceInclusion
        B S hS W W₀) q)) V) x
  exact (congrArg (fun z ↦ (structureSharpRingInverseImage B S hS (subspaceInclusion B S hS W
      W₀)).hom.app V z)
      (app_inverseImage_structureSharpRingInverseImage B S hS (subspaceInclusion B S hS W W₀) q V
          x)).trans
    ((structureSharpRingInverseImage_app B S hS (subspaceInclusion B S hS W W₀) V _).trans
        hcomp.symm)

include hZ hW in
/-- **[Stacks Project, Tag 0618].**  Let `(e₀, c), (e₀, c') : (Z ⊂ X) ⟶ (W₀ ⊂ W)` be two morphisms
of first order thickenings over `T` with the same reduction `e₀` (condition (1)) and the same
map `e₀^*𝒞_{W₀/W} ⟶ 𝒞_{Z/X}` of [Stacks Project, Tag 04CP] (condition (2)).  Then there is an
`𝒪_T`-derivation `D : 𝒪_{W₀} ⟶ (e₀)_*𝒞_{Z/X}` through which the difference of the comorphisms
factors: read as maps `j^{-1}𝒪_W ⟶ (e₀)_*(i^{-1}𝒪_X)`, `c^♯ − (c')^♯ = ι ∘ D ∘ j^♯`. -/
@[stacks 0618 "(a')^♯ − (b')^♯ factors as 𝒪_{Y'} → 𝒪_Y → a_*𝒞_{X/X'} → a_*𝒪_{X'} through an \
𝒪_B-derivation D, read on the small étale site of Y"]
theorem exists_derivation_of_conormalMap_eq (c c' : X ⟶ W)
    (hc : subspaceInclusion B S hS X Z ≫ c = e₀ ≫ subspaceInclusion B S hS W W₀)
    (hc' : subspaceInclusion B S hS X Z ≫ c' = e₀ ≫ subspaceInclusion B S hS W W₀)
    (p : X ⟶ T) (hcq : c ≫ q = p) (hcq' : c' ≫ q = p)
    (hcon : conormalMap B S hS Z W₀ c e₀ hc = conormalMap B S hS Z W₀ c' e₀ hc') :
    ∃ D : PresheafOfModulesOfCommRing.Derivation'
        ((modulePushforward B S hS e₀).obj (conormalModule B S hS X Z)).val
        (structureSharpInverseImage B S hS (subspaceInclusion B S hS W W₀ ≫ q)).hom,
      ∀ (V : (SmallEtale B S hS (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
        (x : ToType ((structureRingSheafInverseImage B S hS (subspaceInclusion B S hS W
            W₀)).obj.obj V)),
        (restrictedSquareZeroValues B S hS Z W₀ e₀ hZ).ι
            (D.d (X := V) ((structureSharpRingInverseImage B S hS (subspaceInclusion B S hS W
                W₀)).hom.app V x)) =
          (restrictedSharpThroughThickening B S hS Z W₀ c e₀ hc).hom.app V x -
            (restrictedSharpThroughThickening B S hS Z W₀ c' e₀ hc').hom.app V x := by
  have := isLocallySurjective_structureSharpRingInverseImage B S hS (subspaceInclusion B S hS W
      W₀) W₀.2.2
  have hcA := comp_eq_comp_algebraicSpaces B S hS Z W₀ e₀ c hc
  have hcA' := comp_eq_comp_algebraicSpaces B S hS Z W₀ e₀ c' hc'
  have hagW := (conormalMap_eq_conormalMap_iff_at B S hS Z W₀ c e₀ hcA hZ c' hcA' _ hc hc').1 hcon
  let L := restrictedLiftDifferenceData B S hS Z W₀ e₀ hZ c c' hc hc'
    (restrictedSharpThroughThickening_eq_of_structureSharpThroughThickeningAt_ι_eq B S hS Z W₀ e₀
      hW c c' hc hc' hagW)
  have hbase :=
    inverseImage_structureSharpRingInverseImage_comp_restrictedSharpThroughThickening_eq_over
      B S hS Z W₀ c c' q e₀ hc hc' (hcq.trans hcq'.symm)
  have hzero : ∀ (V : (SmallEtale B S hS (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
      (s : (inverseImageStructureSheaf B S hS (subspaceInclusion B S hS W W₀ ≫ q)).obj.obj V),
      L.toQuotientDerivation.descend ((structureSharpInverseImage B S hS (subspaceInclusion B S hS
          W W₀ ≫ q)).hom.app V s) =
        0 := fun V s ↦ by
    let iso := (smallEtaleRingedToposHom_compInverseImageRingIso B S hS (subspaceInclusion B S hS
        W W₀) q).app
      (smallEtaleRingedTopos B S hS T).O
    have hs : (iso.hom).hom.app V ((iso.inv).hom.app V s) = s :=
      ConcreteCategory.congr_hom (NatTrans.congr_app (congrArg (fun m => m.hom) iso.inv_hom_id)
        V) s
    have h0 := Stacks.Sites.LiftDifferenceData.descend_eq_zero_of_comp_eq L
      ((inverseImageRingFunctor (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS W
          W₀))).map
        (structureSharpRingInverseImage B S hS q)) _ rfl hbase ((iso.inv).hom.app V s)
    refine Eq.trans ?_ h0
    refine congrArg L.toQuotientDerivation.descend ?_
    exact (congrArg (fun z ↦ (structureSharpInverseImage B S hS (subspaceInclusion B S hS W W₀ ≫
        q)).hom.app V z) hs).symm.trans
      (structureSharpRingInverseImage_app_inverseImage_eq B S hS W₀ q V _).symm
  refine ⟨descendedDerivation B S hS (subspaceInclusion B S hS W W₀ ≫ q) L.toQuotientDerivation
      hzero, fun V x ↦ ?_⟩
  exact (congrArg (restrictedSquareZeroValues B S hS Z W₀ e₀ hZ).ι
    (Stacks.Sites.QuotientDerivation.descend_app L.toQuotientDerivation x)).trans (L.ι_diff x)

end AlgebraicGeometry.Space

end
