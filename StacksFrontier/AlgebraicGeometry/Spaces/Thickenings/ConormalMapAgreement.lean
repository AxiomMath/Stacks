module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ConormalMapComorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftDifferenceSection
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftDifferenceTargetValues

/-!
# Two morphisms of thickenings have the same conormal map iff their comorphisms agree on the ideal

Let `Z ⊂ X` be a first order thickening of algebraic spaces over a scheme `S`, with inclusion
`i : Z ⟶ X`, and let `W₀ ⊆ W` be a closed subspace with inclusion `j : W₀ ⟶ W`.  For two
morphisms `c, c' : X ⟶ W` whose restrictions to `Z` are both `e₀ ≫ j`, the two maps
`e₀^*𝒞_{W₀/W} ⟶ 𝒞_{Z/X}` of conormal modules of [Stacks Project, Tag 04CP] are equal if and only
if the comorphisms of `c` and `c'`, read in the common target `(e₀ ≫ j)_*(i^{-1}𝒪_X)`, agree on
the defining ideal `𝓘_W` of `W₀` in `W`.

This is how condition (2) of [Stacks Project, Tag 0618] is used: in the proof of 0618 the equality
of the two conormal maps is what makes the two comorphisms agree on the ideal, and in the proof
of [Stacks Project, Tag 04D0] agreement on the ideal is what is constructed.

## Main results

* `AlgebraicGeometry.Space.conormalMap_eq_trans_hom_app_comp`: the conormal map of a square,
  unfolded at the level of natural isomorphisms.
* `AlgebraicGeometry.Space.structureSharpThroughThickeningAt_ι_eq_of_transpose_eq` and
  `AlgebraicGeometry.Space.transpose_eq_of_structureSharpThroughThickeningAt_ι_eq`: its two
  directions, at any morphism `F'` equal to `i ≫ c`.
* `AlgebraicGeometry.Space.conormalMap_eq_conormalMap_iff`: the equivalence above.
* `structureSharpThroughThickeningAt_ι_eq_of_restrictedSharpThroughThickening_eq`
  and `restrictedSharpThroughThickening_eq_of_structureSharpThroughThickeningAt_ι_eq`
  (in the namespace `AlgebraicGeometry.Space`):
  when `W₀ ⊂ W` is a first order thickening, agreement on `𝓘_W` on the small étale site of `W` is
  agreement of the transported comorphisms `j^{-1}𝒪_W ⟶ (e₀)_*(i^{-1}𝒪_X)` on the kernel of
  `j^♯ : j^{-1}𝒪_W ⟶ 𝒪_{W₀}`, the form in which [Stacks Project, Tag 0618] uses it.

## Implementation notes

The kernel checks an equation between components at the defining ideal sheaf of the comparison
isomorphisms of [Stacks Project, Tag 03LU] only when the inverse image functors in the two
components are spelled identically: a value `F.obj M` against `F'.obj M` with `F` and `F'`
merely definitionally equal makes it unfold the inverse image functor, which does not terminate.
Two spellings occur.  The comparison `e₀^*j^* ≅ (e₀ ≫ j)^*` composes `e₀ ≫ j` in
`AlgebraicSpaces B S hS`, and a square `i ≫ c = e₀ ≫ j` stated without care composes it in the
full subcategory that abbreviation unfolds to.  So the square is stated here with the composite
taken in `AlgebraicSpaces B S hS`, every step is an instance of a lemma about arbitrary natural
isomorphisms, and the two directions are proved at an arbitrary morphism `F'` equal to `i ≫ c`,
where no second spelling can arise.

## References

* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP)
* [Stacks Project, Tag 0618](https://stacks.math.columbia.edu/tag/0618)
* [Stacks Project, Tag 04D0](https://stacks.math.columbia.edu/tag/04D0)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace CategoryTheory

/-- Two composites `A ≪≫ R` and `A ≪≫ R'` of natural isomorphisms with the same first factor,
evaluated at an object and followed by morphisms `D` and `D'`, are equal exactly when the
composites with the second factors alone are. -/
theorem Iso.trans_hom_app_comp_eq_iff {𝒜 : Type*} {ℬ : Type*} {𝒞 : Type*} {𝒞' : Type*}
    [Category 𝒜] [Category ℬ] [Category 𝒞] [Category 𝒞'] {F₁ F₂ : 𝒜 ⥤ ℬ} {G : 𝒜 ⥤ 𝒞}
    {H : 𝒞 ⥤ ℬ} {G' : 𝒜 ⥤ 𝒞'} {H' : 𝒞' ⥤ ℬ} (A : F₁ ≅ F₂) (R : F₂ ≅ G ⋙ H)
    (R' : F₂ ≅ G' ⋙ H') (M : 𝒜) {N : ℬ} (D : H.obj (G.obj M) ⟶ N)
    (D' : H'.obj (G'.obj M) ⟶ N) :
    (A ≪≫ R).hom.app M ≫ D = (A ≪≫ R').hom.app M ≫ D' ↔
      R.hom.app M ≫ D = R'.hom.app M ≫ D' := by
  simp only [Iso.trans_hom, NatTrans.comp_app, Category.assoc]
  exact ⟨fun h ↦ (cancel_epi _).1 h, fun h ↦ congrArg (A.hom.app M ≫ ·) h⟩

end CategoryTheory

namespace AlgebraicGeometry.Space


variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X W : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)
  (W₀ : ClosedSubspaces B S hS W.1) (c : X ⟶ W)
  (e₀ : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
    (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS))
  -- The composite `e₀ ≫ j` is taken in `AlgebraicSpaces B S hS`, the spelling of
  -- `modulePullbackCompIso`; see the implementation notes.
  (hsq : subspaceInclusion B S hS X Z ≫ c =
    @CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ e₀ (subspaceInclusion B S hS W W₀))

/-! ### Agreement on the ideal, read on the small étale site of `W₀` -/

/-- A commutative square `i ≫ c = e₀ ≫ j`, with the composite `e₀ ≫ j` taken in
`AlgebraicSpaces B S hS`: the spelling `AlgebraicGeometry.Space.conormalMap_eq_conormalMap_iff`
is stated at.  See the implementation notes. -/
theorem comp_eq_comp_algebraicSpaces (c : X ⟶ W)
    (h : subspaceInclusion B S hS X Z ≫ c = e₀ ≫ subspaceInclusion B S hS W W₀) :
    subspaceInclusion B S hS X Z ≫ c =
      @CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ e₀ (subspaceInclusion B S hS W W₀) :=
  h

/-- **Agreement on the defining ideal does not depend on how the common restriction is
written.**  The comorphisms read in `F_*(i^{-1}𝒪_X)` for a morphism `F` equal to `i ≫ c` and to
`i ≫ c'` agree on `𝓘_W` for one spelling of `F` exactly when they do for another; stated with
the equation `F₁ = F₂` explicit, so that two spellings of a composite are identified once, by
`rfl` at the call site, and never inside the direct images. -/
theorem structureSharpThroughThickeningAt_ι_eq_of_eq (c c' : X ⟶ W)
    {F₁ F₂ : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ W} (hF : F₁ = F₂)
    (h₁ : subspaceInclusion B S hS X Z ≫ c = F₁) (h₁' : subspaceInclusion B S hS X Z ≫ c' = F₁)
    (h₂ : subspaceInclusion B S hS X Z ≫ c = F₂) (h₂' : subspaceInclusion B S hS X Z ≫ c' = F₂)
    (hag : ∀ (V : (SmallEtale B S hS W.1)ᵒᵖ)
      (s : (definingIdealSheaf B S hS W W₀).toSheafOfModules.val.obj V),
      (structureSharpThroughThickeningAt B S hS Z c F₁ h₁).hom.app V
          ((definingIdealSheaf B S hS W W₀).ι.val.app V s) =
        (structureSharpThroughThickeningAt B S hS Z c' F₁ h₁').hom.app V
          ((definingIdealSheaf B S hS W W₀).ι.val.app V s))
    (V : (SmallEtale B S hS W.1)ᵒᵖ)
    (s : (definingIdealSheaf B S hS W W₀).toSheafOfModules.val.obj V) :
    (structureSharpThroughThickeningAt B S hS Z c F₂ h₂).hom.app V
        ((definingIdealSheaf B S hS W W₀).ι.val.app V s) =
      (structureSharpThroughThickeningAt B S hS Z c' F₂ h₂').hom.app V
        ((definingIdealSheaf B S hS W W₀).ι.val.app V s) := by
  subst hF
  exact hag V s

section Restricted

variable (hW : IsFirstOrderThickening B S hS W W₀.1)

/-- The direct image along `j` of a morphism of sheaves of rings is, on sections, the direct
image of its underlying morphism of sheaves of sets. -/
theorem app_pushforwardRingFunctor_map_subspaceInclusion
    {Aa : Sheaf (SmallEtale.topology B S hS (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)
        RingCat.{u}}
    (ψ : structureRingSheafInverseImage B S hS (subspaceInclusion B S hS W W₀) ⟶ Aa)
    (V : (SmallEtale B S hS W.1)ᵒᵖ)
    (w : ToType ((pullbackRingSheaf.{u, u, u, u + 1, u, u + 1}
      (SmallEtale.topology B S hS W.1)
      (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS W W₀)).pushforward
      (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS W W₀))).obj.obj V)) :
    ((pushforwardRingFunctor (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS W W₀))).map
        ψ).hom.app V w =
      ((smallToposMorphismTypeU B S hS (subspaceInclusion B S hS W W₀)).pushforward.map
        ((sheafCompose (SmallEtale.topology B S hS (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S
            hS).1)
          (CategoryTheory.forget RingCat.{u})).map ψ)).hom.app V w :=
  setSheafHom_congr_app_apply
    (ringSheafMap_pullbackRingSheafMap (SmallEtale.topology B S hS W.1)
      (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS W W₀)).pushforward ψ) V w

include hW in
/-- **A section of `𝒪_W` killed by `j^♯` is, through the unit `𝒪_W ⟶ j_*j^{-1}𝒪_W`, the direct
image of a section of the conormal module.**  The converse of
`AlgebraicGeometry.Space.exists_app_thickeningRingUnit_eq`: the section is the image of itself
under the identification `𝓘_W ≅ j_*𝒞_{W₀/W}`. -/
theorem exists_pushforward_conormalInverseImageι_eq (V : (SmallEtale B S hS W.1)ᵒᵖ)
    (a : ToType ((structureRingSheaf B S hS W).obj.obj V))
    (ha : (structureSharp B S hS (subspaceInclusion B S hS W W₀)).hom.app V a = 0) :
    ∃ m : ((thickeningTransport B S hS W₀).obj
      ((SheafOfModules.restrictScalars (structureSharpRingInverseImage B S hS
        (subspaceInclusion B S hS W W₀))).obj (conormalModule B S hS W W₀))).val.obj V,
      ((smallToposMorphismTypeU B S hS (subspaceInclusion B S hS W W₀)).pushforward.map
          ((CategoryTheory.Sheaf.moduleSheafFunctor
            (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS W W₀))).map
            (conormalInverseImageι B S hS W₀ hW))).hom.app V m =
        (thickeningRingUnit B S hS W₀).hom.app V a := by
  let k : (SheafOfModules.kerIdeal (structureSharp B S hS (subspaceInclusion B S hS W
      W₀))).toSheafOfModules.val.obj V :=
    ⟨a, (SheafOfModules.mem_kerIdeal _ V a).2 (RingHom.mem_ker.2 ha)⟩
  refine ⟨(conormalDirectImageIso B S hS W₀ hW).hom.val.app V k, ?_⟩
  have hinv := SheafOfModules.iso_inv_hom_app_apply (conormalDirectImageIso B S hS W₀ hW) V k
  have key : ∀ m : ((thickeningTransport B S hS W₀).obj
      ((SheafOfModules.restrictScalars (structureSharpRingInverseImage B S hS
        (subspaceInclusion B S hS W W₀))).obj (conormalModule B S hS W W₀))).val.obj V,
      ((smallToposMorphismTypeU B S hS (subspaceInclusion B S hS W W₀)).pushforward.map
          ((CategoryTheory.Sheaf.moduleSheafFunctor
            (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS W W₀))).map
            (conormalInverseImageι B S hS W₀ hW))).hom.app V m =
        (thickeningRingUnit B S hS W₀).hom.app V
          ((conormalDirectImageIso B S hS W₀ hW).inv.val.app V m).1 := fun m ↦
    SheafOfModules.hom_congr_app_apply
      (Stacks.SheafOfModules.IdealTransport.map_idealι
        (hηiso := isIso_thickeningRingUnit B S hS W₀ hW.1)
        (SmallEtale.topology B S hS W.1) (thickeningToposHom B S hS W₀).pushforward
        (structureSharpRingInverseImage B S hS (subspaceInclusion B S hS W W₀))
        (thickeningRingUnit B S hS W₀)
        (structureSharp B S hS (subspaceInclusion B S hS W W₀))
        (conormalDirectImageIso B S hS W₀ hW)) V m
  refine (key ((conormalDirectImageIso B S hS W₀ hW).hom.val.app V k)).trans ?_
  exact congrArg (fun t : (SheafOfModules.kerIdeal
      (structureSharp B S hS (subspaceInclusion B S hS W W₀))).toSheafOfModules.val.obj V ↦
    (thickeningRingUnit B S hS W₀).hom.app V t.1) hinv

/-- **The comparison `(e₀ ≫ j)_*(i^{-1}𝒪_X) ⟶ j_*(e₀)_*(i^{-1}𝒪_X)` of iterated direct images is
injective on sections**: it has an inverse. -/
theorem app_eq_of_app_pushforwardRingSheafCompInv_eq (V : (SmallEtale B S hS W.1)ᵒᵖ)
    {x y : ToType ((pullbackRingSheaf.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS W.1)
      (smallToposMorphismTypeU B S hS (e₀ ≫ subspaceInclusion B S hS W W₀)).pushforward
      (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z))).obj.obj V)}
    (h : (pushforwardRingSheafCompInv B S hS e₀ (subspaceInclusion B S hS W W₀)
        (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z))).hom.app V x =
      (pushforwardRingSheafCompInv B S hS e₀ (subspaceInclusion B S hS W W₀)
        (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z))).hom.app V y) :
    x = y := by
  have hid := ringSheafHom_congr_app_apply (pushforwardRingSheafCompInv_comp_hom B S hS e₀
      (subspaceInclusion B S hS W W₀)
    (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z))) V
  exact (hid x).symm.trans ((congrArg (fun t ↦ (pushforwardRingSheafCompHom B S hS e₀
      (subspaceInclusion B S hS W W₀)
    (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z))).hom.app V t) h).trans
      (hid y))

include hW in
/-- **Agreement of the transported comorphisms on the kernel of `j^♯` gives agreement of the
comorphisms on the defining ideal.**  A section `a` of `𝓘_W` is killed by `j^♯`, so through the
unit `𝒪_W ⟶ j_*j^{-1}𝒪_W` it is the direct image of a section of the conormal module of
`W₀ ⊂ W`, on which the two transported comorphisms agree.  The comorphisms read in
`(e₀ ≫ j)_*(i^{-1}𝒪_X)` are recovered from the transported ones through the unit and the
comparison of iterated direct images, which is invertible. -/
theorem structureSharpThroughThickeningAt_ι_eq_of_restrictedSharpThroughThickening_eq
    (c c' : X ⟶ W) (hc : subspaceInclusion B S hS X Z ≫ c = e₀ ≫ subspaceInclusion B S hS W W₀)
    (hc' : subspaceInclusion B S hS X Z ≫ c' = e₀ ≫ subspaceInclusion B S hS W W₀)
    (hag : ∀ (V : (SmallEtale B S hS (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
      (x : ToType ((structureRingSheafInverseImage B S hS (subspaceInclusion B S hS W W₀)).obj.obj
          V)),
      (structureSharpRingInverseImage B S hS (subspaceInclusion B S hS W W₀)).hom.app V x = 0 →
        (restrictedSharpThroughThickening B S hS Z W₀ c e₀ hc).hom.app V x =
          (restrictedSharpThroughThickening B S hS Z W₀ c' e₀ hc').hom.app V x)
    (V : (SmallEtale B S hS W.1)ᵒᵖ)
    (s : (definingIdealSheaf B S hS W W₀).toSheafOfModules.val.obj V) :
    (structureSharpThroughThickeningAt B S hS Z c (e₀ ≫ subspaceInclusion B S hS W W₀) hc).hom.app V
        ((definingIdealSheaf B S hS W W₀).ι.val.app V s) =
      (structureSharpThroughThickeningAt B S hS Z c' (e₀ ≫ subspaceInclusion B S hS W W₀)
          hc').hom.app V
        ((definingIdealSheaf B S hS W W₀).ι.val.app V s) := by
  have ha : (structureSharp B S hS (subspaceInclusion B S hS W W₀)).hom.app V
      ((definingIdealSheaf B S hS W W₀).ι.val.app V s) = 0 :=
    RingHom.mem_ker.1 ((SheafOfModules.mem_kerIdeal _ V _).1 s.2)
  obtain ⟨m, hm⟩ := exists_pushforward_conormalInverseImageι_eq B S hS W₀ hW V _ ha
  have hset : (CategoryTheory.Sheaf.moduleSheafFunctor
        (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS W W₀))).map
          (conormalInverseImageι B S hS W₀ hW) ≫
        (sheafCompose (SmallEtale.topology B S hS (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S
            hS).1)
          (CategoryTheory.forget RingCat.{u})).map
          (restrictedSharpThroughThickening B S hS Z W₀ c e₀ hc) =
      (CategoryTheory.Sheaf.moduleSheafFunctor
        (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS W W₀))).map
          (conormalInverseImageι B S hS W₀ hW) ≫
        (sheafCompose (SmallEtale.topology B S hS (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S
            hS).1)
          (CategoryTheory.forget RingCat.{u})).map
          (restrictedSharpThroughThickening B S hS Z W₀ c' e₀ hc') :=
    CategoryTheory.Sheaf.hom_ext_sections fun V' m' ↦
      hag V' _ (app_conormalInverseImageι_eq_zero B S hS W₀ hW V' m')
  have hpush := setSheafHom_congr_app_apply
    (congrArg (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS W W₀)).pushforward.map
        hset) V m
  have key : ∀ (c : X ⟶ W)
      (hc : subspaceInclusion B S hS X Z ≫ c = e₀ ≫ subspaceInclusion B S hS W W₀),
      (ringUnit (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS W W₀))
          (structureRingSheaf B S hS W) ≫
        (pushforwardRingFunctor (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS W
            W₀))).map
          (restrictedSharpThroughThickening B S hS Z W₀ c e₀ hc)).hom.app V
          ((definingIdealSheaf B S hS W W₀).ι.val.app V s) =
      ((smallToposMorphismTypeU B S hS (subspaceInclusion B S hS W W₀)).pushforward.map
        ((CategoryTheory.Sheaf.moduleSheafFunctor
          (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS W W₀))).map
            (conormalInverseImageι B S hS W₀ hW) ≫
          (sheafCompose (SmallEtale.topology B S hS (⟨W₀.1.toFunctor, W₀.2.1⟩ :
            AlgebraicSpaces B S hS).1) (CategoryTheory.forget RingCat.{u})).map
            (restrictedSharpThroughThickening B S hS Z W₀ c e₀ hc))).hom.app V m := fun c hc ↦ by
    refine (congrArg (fun t ↦ ((pushforwardRingFunctor (smallToposMorphismTypeU B S hS
        (subspaceInclusion B S hS W W₀))).map
      (restrictedSharpThroughThickening B S hS Z W₀ c e₀ hc)).hom.app V t) hm.symm).trans ?_
    refine (app_pushforwardRingFunctor_map_subspaceInclusion B S hS W₀ _ V _).trans ?_
    exact setSheafHom_congr_app_apply ((smallToposMorphismTypeU B S hS (subspaceInclusion B S hS
        W W₀)).pushforward.map_comp _ _).symm V m
  exact app_eq_of_app_pushforwardRingSheafCompInv_eq B S hS Z W₀ e₀ V
    ((ringSheafHom_congr_app_apply
      (ringUnit_comp_map_restrictedSharpThroughThickening B S hS Z W₀ c e₀ hc) V _).symm.trans
      (((key c hc).trans (hpush.trans (key c' hc').symm)).trans (ringSheafHom_congr_app_apply
        (ringUnit_comp_map_restrictedSharpThroughThickening B S hS Z W₀ c' e₀ hc') V _)))

/-- Agreement of the comorphisms on the sections of `𝓘_W` is agreement on the sections of `𝒪_W`
killed by `j^♯`: these are the same sections. -/
theorem structureSharpThroughThickeningAt_eq_of_app_eq_zero
    (c c' : X ⟶ W) (hc : subspaceInclusion B S hS X Z ≫ c = e₀ ≫ subspaceInclusion B S hS W W₀)
    (hc' : subspaceInclusion B S hS X Z ≫ c' = e₀ ≫ subspaceInclusion B S hS W W₀)
    (hag : ∀ (V : (SmallEtale B S hS W.1)ᵒᵖ)
      (s : (definingIdealSheaf B S hS W W₀).toSheafOfModules.val.obj V),
      (structureSharpThroughThickeningAt B S hS Z c (e₀ ≫ subspaceInclusion B S hS W W₀)
          hc).hom.app V
          ((definingIdealSheaf B S hS W W₀).ι.val.app V s) =
        (structureSharpThroughThickeningAt B S hS Z c' (e₀ ≫ subspaceInclusion B S hS W W₀)
            hc').hom.app V
          ((definingIdealSheaf B S hS W W₀).ι.val.app V s))
    (V : (SmallEtale B S hS W.1)ᵒᵖ) (a : ToType ((structureRingSheaf B S hS W).obj.obj V))
    (ha : (structureSharp B S hS (subspaceInclusion B S hS W W₀)).hom.app V a = 0) :
    (structureSharpThroughThickeningAt B S hS Z c (e₀ ≫ subspaceInclusion B S hS W W₀) hc).hom.app
        V a =
      (structureSharpThroughThickeningAt B S hS Z c' (e₀ ≫ subspaceInclusion B S hS W W₀)
          hc').hom.app V a := by
  let t : (definingIdealSheaf B S hS W W₀).toSheafOfModules.val.obj V :=
    ⟨a, (mem_definingIdealAt_iff B S hS W W₀ V a).2 ha⟩
  have ht : (definingIdealSheaf B S hS W W₀).ι.val.app V t = a := rfl
  exact ht ▸ hag V t

include hW in
/-- **Agreement of the comorphisms on the defining ideal gives agreement of the transported
comorphisms on the kernel of `j^♯`.**  This is
`AlgebraicGeometry.Space.app_eq_of_app_eq_zero_of_app_thickeningRingUnit_eq` for the first
order thickening `W₀ ⊂ W`: a section of `𝒪_W` killed by `j^♯` is a section of `𝓘_W`, and through
the unit and the comparison of iterated direct images the transported comorphisms there are the
comorphisms read in `(e₀ ≫ j)_*(i^{-1}𝒪_X)`. -/
theorem restrictedSharpThroughThickening_eq_of_structureSharpThroughThickeningAt_ι_eq
    (c c' : X ⟶ W) (hc : subspaceInclusion B S hS X Z ≫ c = e₀ ≫ subspaceInclusion B S hS W W₀)
    (hc' : subspaceInclusion B S hS X Z ≫ c' = e₀ ≫ subspaceInclusion B S hS W W₀)
    (hag : ∀ (V : (SmallEtale B S hS W.1)ᵒᵖ)
      (s : (definingIdealSheaf B S hS W W₀).toSheafOfModules.val.obj V),
      (structureSharpThroughThickeningAt B S hS Z c (e₀ ≫ subspaceInclusion B S hS W W₀)
          hc).hom.app V
          ((definingIdealSheaf B S hS W W₀).ι.val.app V s) =
        (structureSharpThroughThickeningAt B S hS Z c' (e₀ ≫ subspaceInclusion B S hS W W₀)
            hc').hom.app V
          ((definingIdealSheaf B S hS W W₀).ι.val.app V s))
    (V : (SmallEtale B S hS (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
    (x : ToType ((structureRingSheafInverseImage B S hS (subspaceInclusion B S hS W W₀)).obj.obj V))
    (hx : (structureSharpRingInverseImage B S hS (subspaceInclusion B S hS W W₀)).hom.app V x = 0) :
    (restrictedSharpThroughThickening B S hS Z W₀ c e₀ hc).hom.app V x =
      (restrictedSharpThroughThickening B S hS Z W₀ c' e₀ hc').hom.app V x :=
  app_eq_of_app_eq_zero_of_app_thickeningRingUnit_eq B S hS W₀ hW _ _
    (fun V' a ha ↦
      (ringSheafHom_congr_app_apply
        (ringUnit_comp_map_restrictedSharpThroughThickening B S hS Z W₀ c e₀ hc) V' a).trans
        ((congrArg ((pushforwardRingSheafCompInv B S hS e₀ (subspaceInclusion B S hS W W₀)
            (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z))).hom.app V')
          (structureSharpThroughThickeningAt_eq_of_app_eq_zero B S hS Z W₀ e₀ c c' hc hc' hag V'
            a ha)).trans
          (ringSheafHom_congr_app_apply
            (ringUnit_comp_map_restrictedSharpThroughThickening B S hS Z W₀ c' e₀ hc') V'
              a).symm))
    V x hx

end Restricted

section Comparison

-- Unfolding the inverse image of modules to its construction does not terminate, and is not
-- needed: the identifications below are between composites of named comparisons.
attribute [local irreducible] modulePullback

/-- The conormal map of a square is its comparison factor, evaluated at the defining ideal sheaf,
followed by `i^*` of the map of defining ideal sheaves. -/
theorem conormalMap_eq_conormalPullbackCompIso_hom_app_comp :
    conormalMap B S hS Z W₀ c e₀ hsq =
      (conormalPullbackCompIso B S hS Z W₀ c e₀ hsq).hom.app
          (definingIdealSheaf B S hS W W₀).toSheafOfModules ≫
        (modulePullback B S hS (subspaceInclusion B S hS X Z)).map
          (idealSheafMap B S hS Z W₀ c e₀ hsq) :=
  rfl

/-- The comparison `e₀^*j^* ≅ i^*c^*` of a square, unfolded. -/
theorem conormalPullbackCompIso_eq :
    conormalPullbackCompIso B S hS Z W₀ c e₀ hsq =
      modulePullbackCompIso B S hS e₀ (subspaceInclusion B S hS W W₀) ≪≫
          eqToIso (congrArg (fun g ↦ modulePullback B S hS g) hsq.symm) ≪≫
          (modulePullbackCompIso B S hS (subspaceInclusion B S hS X Z) c).symm :=
  rfl

/-- **The conormal map of a square, unfolded**: the comparison `e₀^*j^* ≅ (e₀ ≫ j)^*` of
[Stacks Project, Tag 03LU], the renaming `(e₀ ≫ j)^* = (i ≫ c)^*` along the square, the
comparison `(i ≫ c)^* ≅ i^*c^*`, and `i^*` of the map of defining ideal sheaves. -/
theorem conormalMap_eq_trans_hom_app_comp :
    conormalMap B S hS Z W₀ c e₀ hsq =
      (modulePullbackCompIso B S hS e₀ (subspaceInclusion B S hS W W₀) ≪≫
          eqToIso (congrArg (fun g ↦ modulePullback B S hS g) hsq.symm) ≪≫
          (modulePullbackCompIso B S hS (subspaceInclusion B S hS X Z) c).symm).hom.app
          (definingIdealSheaf B S hS W W₀).toSheafOfModules ≫
        (modulePullback B S hS (subspaceInclusion B S hS X Z)).map
          (idealSheafMap B S hS Z W₀ c e₀ hsq) :=
  (conormalMap_eq_conormalPullbackCompIso_hom_app_comp B S hS Z W₀ c e₀ hsq).trans
    (congrArg (fun φ ↦ φ.hom.app (definingIdealSheaf B S hS W W₀).toSheafOfModules ≫
        (modulePullback B S hS (subspaceInclusion B S hS X Z)).map
          (idealSheafMap B S hS Z W₀ c e₀ hsq))
      (conormalPullbackCompIso_eq B S hS Z W₀ c e₀ hsq))

variable (hZ : IsFirstOrderThickening B S hS X Z.1)

/-- `AlgebraicGeometry.Space.pushforward_conormalSetInclusion_homEquiv_at` with the renaming
`F'^* = (i ≫ c)^*` and the inverse of the comparison `(i ≫ c)^* ≅ i^*c^*` composed as natural
isomorphisms, the shape in which they occur in `AlgebraicGeometry.Space.conormalMap`. -/
theorem pushforward_conormalSetInclusion_homEquiv_trans
    (F' : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ W)
    (h : subspaceInclusion B S hS X Z ≫ c = F')
    (V : (SmallEtale B S hS W.1)ᵒᵖ)
    (s : (definingIdealSheaf B S hS W W₀).toSheafOfModules.val.obj V) :
    ((smallToposMorphismTypeU B S hS F').pushforward.map
        (conormalSetInclusion B S hS Z hZ)).hom.app V
        (((modulePullbackAdjunction B S hS F').homEquiv _ _
          ((eqToIso (congrArg (fun g ↦ modulePullback B S hS g) h.symm) ≪≫
              (modulePullbackCompIso B S hS (subspaceInclusion B S hS X Z) c).symm).hom.app
              (definingIdealSheaf B S hS W W₀).toSheafOfModules ≫
            (modulePullback B S hS (subspaceInclusion B S hS X Z)).map
              (idealSheafMap B S hS Z W₀ c e₀ hsq))).val.app V s) =
      (structureSharpThroughThickeningAt B S hS Z c F' h).hom.app V
        ((definingIdealSheaf B S hS W W₀).ι.val.app V s) := by
  subst h
  simp only [eqToIso_refl, Iso.refl_trans, Iso.symm_hom, structureSharpThroughThickeningAt,
    eqToHom_refl, Category.comp_id]
  exact pushforward_conormalSetInclusion_homEquiv B S hS Z W₀ c e₀ hsq hZ V s

section Agreement

variable (c' : X ⟶ W) (hsq' : subspaceInclusion B S hS X Z ≫ c' =
    @CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ e₀ (subspaceInclusion B S hS W W₀))
  (F' : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ W)
  (h : subspaceInclusion B S hS X Z ≫ c = F') (h' : subspaceInclusion B S hS X Z ≫ c' = F')

include hZ in
/-- Equal morphisms `(i ≫ c)^*𝓘_W ⟶ 𝒞_{Z/X}` give comorphisms which agree on `𝓘_W`. -/
theorem structureSharpThroughThickeningAt_ι_eq_of_transpose_eq
    (hm : ((eqToIso (congrArg (fun g ↦ modulePullback B S hS g) h.symm) ≪≫
          (modulePullbackCompIso B S hS (subspaceInclusion B S hS X Z) c).symm).hom.app
          (definingIdealSheaf B S hS W W₀).toSheafOfModules ≫
        (modulePullback B S hS (subspaceInclusion B S hS X Z)).map
          (idealSheafMap B S hS Z W₀ c e₀ hsq)) =
      ((eqToIso (congrArg (fun g ↦ modulePullback B S hS g) h'.symm) ≪≫
          (modulePullbackCompIso B S hS (subspaceInclusion B S hS X Z) c').symm).hom.app
          (definingIdealSheaf B S hS W W₀).toSheafOfModules ≫
        (modulePullback B S hS (subspaceInclusion B S hS X Z)).map
          (idealSheafMap B S hS Z W₀ c' e₀ hsq')))
    (V : (SmallEtale B S hS W.1)ᵒᵖ)
    (s : (definingIdealSheaf B S hS W W₀).toSheafOfModules.val.obj V) :
    (structureSharpThroughThickeningAt B S hS Z c F' h).hom.app V
        ((definingIdealSheaf B S hS W W₀).ι.val.app V s) =
      (structureSharpThroughThickeningAt B S hS Z c' F' h').hom.app V
        ((definingIdealSheaf B S hS W W₀).ι.val.app V s) :=
  (pushforward_conormalSetInclusion_homEquiv_trans B S hS Z W₀ c e₀ hsq hZ F' h V s).symm.trans
    ((congrArg (fun m ↦ ((smallToposMorphismTypeU B S hS
        F').pushforward.map
          (conormalSetInclusion B S hS Z hZ)).hom.app V
      (((modulePullbackAdjunction B S hS F').homEquiv _ _
        m).val.app V s)) hm).trans
      (pushforward_conormalSetInclusion_homEquiv_trans B S hS Z W₀ c' e₀ hsq' hZ F' h' V s))

include hZ in
/-- Comorphisms which agree on `𝓘_W` give equal morphisms `(i ≫ c)^*𝓘_W ⟶ 𝒞_{Z/X}`. -/
theorem transpose_eq_of_structureSharpThroughThickeningAt_ι_eq
    (hag : ∀ (V : (SmallEtale B S hS W.1)ᵒᵖ)
      (s : (definingIdealSheaf B S hS W W₀).toSheafOfModules.val.obj V),
      (structureSharpThroughThickeningAt B S hS Z c F' h).hom.app V
          ((definingIdealSheaf B S hS W W₀).ι.val.app V s) =
        (structureSharpThroughThickeningAt B S hS Z c' F' h').hom.app V
          ((definingIdealSheaf B S hS W W₀).ι.val.app V s)) :
    ((eqToIso (congrArg (fun g ↦ modulePullback B S hS g) h.symm) ≪≫
          (modulePullbackCompIso B S hS (subspaceInclusion B S hS X Z) c).symm).hom.app
          (definingIdealSheaf B S hS W W₀).toSheafOfModules ≫
        (modulePullback B S hS (subspaceInclusion B S hS X Z)).map
          (idealSheafMap B S hS Z W₀ c e₀ hsq)) =
      ((eqToIso (congrArg (fun g ↦ modulePullback B S hS g) h'.symm) ≪≫
          (modulePullbackCompIso B S hS (subspaceInclusion B S hS X Z) c').symm).hom.app
          (definingIdealSheaf B S hS W W₀).toSheafOfModules ≫
        (modulePullback B S hS (subspaceInclusion B S hS X Z)).map
          (idealSheafMap B S hS Z W₀ c' e₀ hsq')) := by
  have := mono_pushforward_map_conormalSetInclusion B S hS Z hZ F'
  refine ((modulePullbackAdjunction B S hS F').homEquiv _ _).injective ?_
  have hsets := (cancel_mono ((smallToposMorphismTypeU B S hS F').pushforward.map
      (conormalSetInclusion B S hS Z hZ))).1
    (CategoryTheory.Sheaf.hom_ext_sections fun V s ↦
      ((pushforward_conormalSetInclusion_homEquiv_trans B S hS Z W₀ c e₀ hsq hZ F' h V s).trans
        ((hag V s).trans
          (pushforward_conormalSetInclusion_homEquiv_trans B S hS Z W₀ c' e₀ hsq' hZ F' h' V
            s).symm)) :
      (CategoryTheory.Sheaf.moduleSheafFunctor (structureRingSheaf B S hS W)).map
          ((modulePullbackAdjunction B S hS F').homEquiv _ _
            (((eqToIso (congrArg (fun g ↦ modulePullback B S hS g) h.symm) ≪≫
          (modulePullbackCompIso B S hS (subspaceInclusion B S hS X Z) c).symm).hom.app
          (definingIdealSheaf B S hS W W₀).toSheafOfModules ≫
        (modulePullback B S hS (subspaceInclusion B S hS X Z)).map
          (idealSheafMap B S hS Z W₀ c e₀ hsq)))) ≫
        (smallToposMorphismTypeU B S hS F').pushforward.map
          (conormalSetInclusion B S hS Z hZ) =
      (CategoryTheory.Sheaf.moduleSheafFunctor (structureRingSheaf B S hS W)).map
          ((modulePullbackAdjunction B S hS F').homEquiv _ _
            (((eqToIso (congrArg (fun g ↦ modulePullback B S hS g) h'.symm) ≪≫
          (modulePullbackCompIso B S hS (subspaceInclusion B S hS X Z) c').symm).hom.app
          (definingIdealSheaf B S hS W W₀).toSheafOfModules ≫
        (modulePullback B S hS (subspaceInclusion B S hS X Z)).map
          (idealSheafMap B S hS Z W₀ c' e₀ hsq')))) ≫
        (smallToposMorphismTypeU B S hS F').pushforward.map
          (conormalSetInclusion B S hS Z hZ))
  exact SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V ↦
    ModuleCat.hom_ext (LinearMap.ext fun s ↦ setSheafHom_congr_app_apply hsets V s))

include hZ in
/-- **[Stacks Project, Tag 04CP] against the comorphisms.**  For two morphisms `c, c' : X ⟶ W`
whose restrictions to the first order thickening `Z ⊂ X` are both `e₀ ≫ j`, the two maps
`e₀^*𝒞_{W₀/W} ⟶ 𝒞_{Z/X}` of conormal modules are equal if and only if the comorphisms of `c` and
`c'`, read in the common target `(e₀ ≫ j)_*(i^{-1}𝒪_X)`, agree on the defining ideal `𝓘_W` of
`W₀` in `W`. -/
theorem conormalMap_eq_conormalMap_iff :
    conormalMap B S hS Z W₀ c e₀ hsq = conormalMap B S hS Z W₀ c' e₀ hsq' ↔
      ∀ (V : (SmallEtale B S hS W.1)ᵒᵖ)
        (s : (definingIdealSheaf B S hS W W₀).toSheafOfModules.val.obj V),
        (structureSharpThroughThickeningAt B S hS Z c _ hsq).hom.app V
            ((definingIdealSheaf B S hS W W₀).ι.val.app V s) =
          (structureSharpThroughThickeningAt B S hS Z c' _ hsq').hom.app V
            ((definingIdealSheaf B S hS W W₀).ι.val.app V s) :=
  (Eq.congr (conormalMap_eq_trans_hom_app_comp B S hS Z W₀ c e₀ hsq)
    (conormalMap_eq_trans_hom_app_comp B S hS Z W₀ c' e₀ hsq')).trans
    ((Iso.trans_hom_app_comp_eq_iff _ _ _ _ _ _).trans
      ⟨structureSharpThroughThickeningAt_ι_eq_of_transpose_eq B S hS Z W₀ c e₀ hsq hZ
          c' hsq' _ hsq hsq',
        transpose_eq_of_structureSharpThroughThickeningAt_ι_eq B S hS Z W₀ c e₀ hsq hZ
          c' hsq' _ hsq hsq'⟩)

include hZ in
/-- `AlgebraicGeometry.Space.conormalMap_eq_conormalMap_iff` with the comorphisms read in
`F'_*(i^{-1}𝒪_X)` for any morphism `F'` equal to `i ≫ c` and to `i ≫ c'`, however it is spelled:
the identification with `e₀ ≫ j` is made by the equations, never by unfolding. -/
theorem conormalMap_eq_conormalMap_iff_at :
    conormalMap B S hS Z W₀ c e₀ hsq = conormalMap B S hS Z W₀ c' e₀ hsq' ↔
      ∀ (V : (SmallEtale B S hS W.1)ᵒᵖ)
        (s : (definingIdealSheaf B S hS W W₀).toSheafOfModules.val.obj V),
        (structureSharpThroughThickeningAt B S hS Z c F' h).hom.app V
            ((definingIdealSheaf B S hS W W₀).ι.val.app V s) =
          (structureSharpThroughThickeningAt B S hS Z c' F' h').hom.app V
            ((definingIdealSheaf B S hS W W₀).ι.val.app V s) :=
  (conormalMap_eq_conormalMap_iff B S hS Z W₀ c e₀ hsq hZ c' hsq').trans
    ⟨fun H ↦ structureSharpThroughThickeningAt_ι_eq_of_eq B S hS Z W₀ c c' (hsq.symm.trans h)
        hsq hsq' h h' H,
      fun H ↦ structureSharpThroughThickeningAt_ι_eq_of_eq B S hS Z W₀ c c' (h.symm.trans hsq)
        h h' hsq hsq' H⟩

end Agreement

end Comparison

end AlgebraicGeometry.Space

end
