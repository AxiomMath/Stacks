module

public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFreeOfRank
public import StacksFrontier.AlgebraicGeometry.Spaces.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierEtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.Defs
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallyUnramifiedEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.RestrictSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeAsSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkAsPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.FirstOrderAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.Order
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.UniversalExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversalFirstOrderThickeningDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversalThickeningOfFormallyUnramified
public import StacksFrontier.AlgebraicGeometry.Thickenings
public import StacksFrontier.CategoryTheory.Sites.Localization.Relocalize

/-!
# The universal first-order thickening of a cover over a deformation of its target

In the deformation problem `AlgebraicGeometry.Stack.FiniteHilbert.HasCoverDeformations` of
**Stacks 06D8** — a first-order thickening `U ⊂ U'` of affine objects of the big fppf site, an
algebraic space `X'` over `U'`, a degree-`d` finite locally free cover `Z ⟶ U` and an unramified
morphism `f : Z ⟶ U ×_{U'} X'` — the source works with the universal first-order thickening `Z'`
of `Z` over `X'`. This file produces it as an affine object `W` of the big fppf site of `U'`,
with the space-level universal property of **Stacks 0602** for the range of `Z ⟶ W` and with
`Z ⟶ W` a first-order thickening of schemes.

## Main results

* `AlgebraicGeometry.Space.formallyUnramified_yonedaEquiv_symm_of_relocalizeRestrict`: a morphism
  into the restriction of a presheaf along a monomorphism `A ⟶ A'` of the base which is formally
  unramified over `A` names a formally unramified morphism over `A'`.
* `AlgebraicGeometry.Space.isFirstOrderThickening_scheme_of_range_yoneda_map`: over an affine
  target, a morphism of the site whose range is a space-level first-order thickening is a
  first-order thickening of schemes.
* `AlgebraicGeometry.Space.exists_universalThickening_range_yoneda_map_of_ambientIso`: a universal
  first-order thickening whose ambient space is represented by an affine object `W`, read as a
  first-order thickening `Z ⟶ W` of the site.
* `AlgebraicGeometry.Stack.FiniteHilbert.exists_universalThickening_scheme_of_coverDeformationData`
  is the universal first-order thickening of `Z` over `X'`, as an affine object of the site.

## References

* [Stacks Project, Tag 0602](https://stacks.math.columbia.edu/tag/0602)
* [Stacks Project, Tag 0605](https://stacks.math.columbia.edu/tag/0605)
* [Stacks Project, Tag 0606](https://stacks.math.columbia.edu/tag/0606)
* [Stacks Project, Tag 04GA](https://stacks.math.columbia.edu/tag/04GA)
* [Stacks Project, Tag 05ZR](https://stacks.math.columbia.edu/tag/05ZR)
* [Stacks Project, Tag 06D8](https://stacks.math.columbia.edu/tag/06D8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}}

/-- Products of presheaves on `BigFppfOver B S hS`, given directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) hasLimitsOfShape_discrete_presheaf_CoverDeformationThickening
    {S : Scheme.{u}} {hS : B.Contains S} (J : Type) :
    HasLimitsOfShape (Discrete J) ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  functorCategoryHasLimitsOfShape

/-- **Formal unramifiedness along a monomorphism of the base.** Let `m : A ⟶ A'` be a monomorphism
of the big fppf category, `F'` a presheaf on the big fppf site of `A'`, `P` an object of the big
fppf site of `A` and `f : P ⟶ F'|_A` a morphism into the restriction of `F'`. If `f` is formally
unramified over `A`, then the morphism `P ⟶ F'` it names over `A'` is formally unramified. -/
theorem formallyUnramified_yonedaEquiv_symm_of_relocalizeRestrict {A A' : Scheme.{u}}
    {hA : B.Contains A} {hA' : B.Contains A'} (m : B.obj hA ⟶ B.obj hA') [Mono m]
    (F' : (BigFppfOver B A' hA')ᵒᵖ ⥤ Type u) (P : BigFppfOver B A hA)
    (f : yoneda.obj P ⟶ (OverShriek.relocalizeRestrict m).obj F')
    (hf : FormallyUnramified (B := B) (S := A) (hS := hA) f) :
    FormallyUnramified (B := B) (S := A') (hS := hA') (yonedaEquiv.symm
      ((yonedaEquiv f : ((OverShriek.relocalizeRestrict m).obj F').obj (op P)) :
        F'.obj (op ((Over.map m).obj P)))) := by
  set xx : yoneda.obj ((Over.map m).obj P) ⟶ F' := yonedaEquiv.symm
    ((yonedaEquiv f : ((OverShriek.relocalizeRestrict m).obj F').obj (op P)) :
      F'.obj (op ((Over.map m).obj P))) with hxx
  intro T T' hT hT' k hk x₀ y hxy z₁ z₂ hz₁ hz₂
  have hw : ∀ z : T' ⟶ (Over.map m).obj P, z.left ≫ P.hom ≫ m = T'.hom := fun z => Over.w z
  have hq : z₂.left ≫ P.hom = z₁.left ≫ P.hom := by
    rw [← cancel_mono m, Category.assoc, Category.assoc, hw, hw]
  let T'A : BigFppfOver B A hA := Over.mk (z₁.left ≫ P.hom)
  let TA : BigFppfOver B A hA := Over.mk (k.left ≫ z₁.left ≫ P.hom)
  let kA : TA ⟶ T'A := Over.homMk k.left
  let e : (Over.map m).obj T'A ⟶ T' := Over.homMk (𝟙 _) (by
    simp only [Over.map_obj_left, Over.mk_left, Over.map_obj_hom, Over.mk_hom, Category.id_comp,
      T'A, Category.assoc]
    exact (hw z₁).symm)
  let w₁ : T'A ⟶ P := Over.homMk z₁.left
  let w₂ : T'A ⟶ P := Over.homMk z₂.left hq
  have hmapw : ∀ (w : T'A ⟶ P) (z : T' ⟶ (Over.map m).obj P), w.left = z.left →
      (Over.map m).map w = e ≫ z := fun w z h => by
    ext
    simp [e, h]
  have happ : ∀ (w : T'A ⟶ P) (z : T' ⟶ (Over.map m).obj P), w.left = z.left →
      f.app (op T'A) w = F'.map e.op (xx.app (op T') z) := fun w z h => by
    let u : F'.obj (op ((Over.map m).obj P)) :=
      (yonedaEquiv f : ((OverShriek.relocalizeRestrict m).obj F').obj (op P))
    calc f.app (op T'A) w = F'.map ((Over.map m).map w).op u := (map_yonedaEquiv f w).symm
      _ = F'.map (e ≫ z).op u := by rw [hmapw w z h]
      _ = F'.map e.op (F'.map z.op u) := by rw [op_comp, Functor.map_comp_apply]
      _ = F'.map e.op (xx.app (op T') z) := by rw [hxx]; rfl
  have h₁ : f.app (op T'A) w₁ = F'.map e.op y := by rw [happ w₁ z₁ rfl, hz₁.2]
  have h₂ : f.app (op T'A) w₂ = F'.map e.op y := by rw [happ w₂ z₂ rfl, hz₂.2]
  have hk₁₂ : kA ≫ w₂ = kA ≫ w₁ :=
    Over.OverMorphism.ext (congrArg (fun g => g.left) (hz₂.1.trans hz₁.1.symm))
  have key : w₁ = w₂ := hf TA T'A hT hT' kA hk (kA ≫ w₁) (F'.map e.op y)
    (by
      rw [← h₁]
      exact NatTrans.naturality_apply f kA.op w₁)
    w₁ w₂ ⟨rfl, h₁⟩ ⟨hk₁₂, h₂⟩
  exact Over.OverMorphism.ext (show z₁.left = z₂.left from congrArg (fun g => g.left) key)

/-- **A first-order thickening of the algebraic space of an affine object, cut out by a
morphism of the site, is a first-order thickening of schemes.** Let `j : V ⟶ W` be a morphism of
the big fppf category over `S` with `W` affine and `yoneda.map j` a monomorphism. If the range of
`yoneda.map j` is a first-order thickening of the algebraic space represented by `W`, then the
underlying morphism of schemes of `j` is a closed immersion with square-zero kernel.

This is the converse of `AlgebraicGeometry.Space.isFirstOrderThickening_range_yoneda_map` over an
affine target. -/
theorem isFirstOrderThickening_scheme_of_range_yoneda_map {S : Scheme.{u}} {hS : B.Contains S}
    {V W : BigFppfOver B S hS} (j : V ⟶ W) [Mono (yoneda.map j)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj W)]
    (h : IsFirstOrderThickening B S hS (AlgebraicGeometry.schemeSpace W)
      (Subfunctor.range (yoneda.map j))) :
    Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map j) := by
  obtain ⟨hG, hsq⟩ := h
  let Z : ClosedSubspaces B S hS (AlgebraicGeometry.schemeSpace W).1 :=
    ⟨Subfunctor.range (yoneda.map j), hG.1⟩
  let U := idChart B S hS W
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj U.1.left) :=
    inferInstanceAs (IsAffine ((BigFppfOver.toScheme B S hS).obj W))
  obtain ⟨P, s, t, hpb, hci, hker⟩ : ∃ (P : BigFppfOver B S hS) (s : P ⟶ W)
      (t : yoneda.obj P ⟶ (Subfunctor.range (yoneda.map j)).toFunctor),
      IsPullback t (yoneda.map s) (Subfunctor.range (yoneda.map j)).ι (𝟙 (yoneda.obj W)) ∧
      AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map s) ∧
      ((BigFppfOver.toScheme B S hS).map s).ker = Scheme.IdealSheafData.ofIdealTop
        (definingIdealAt B S hS (AlgebraicGeometry.schemeSpace W) Z (op U)) :=
    ⟨_, _, _, Z.2.2.rep.isPullback U.1.hom, Z.2.2.property_snd _,
      ker_rep_snd_eq_ofIdealTop_definingIdealAt B S hS (AlgebraicGeometry.schemeSpace W) Z U⟩
  have h2 : definingIdealAt B S hS (AlgebraicGeometry.schemeSpace W) Z (op U) ^ 2 = ⊥ := hsq U
  have : IsIso t := hpb.isIso_fst_of_isIso
  obtain ⟨e, he⟩ := yoneda.map_surjective (t ≫ inv (Subfunctor.toRange (yoneda.map j)))
  have : IsIso (yoneda.map e) := by rw [he]; infer_instance
  have : IsIso e := isIso_of_fully_faithful yoneda e
  have hs : s = e ≫ j := by
    refine yoneda.map_injective ?_
    have hι : inv (Subfunctor.toRange (yoneda.map j)) ≫ yoneda.map j =
        (Subfunctor.range (yoneda.map j)).ι := by
      rw [IsIso.inv_comp_eq, Subfunctor.toRange_ι]
    rw [Functor.map_comp, he, Category.assoc, hι]
    simpa using hpb.w.symm
  subst hs
  rw [Functor.map_comp] at hci hker
  refine ⟨(MorphismProperty.cancel_left_of_respectsIso
    (@AlgebraicGeometry.IsClosedImmersion.{u}) _ _).1 hci, ?_⟩
  rw [Scheme.Hom.ker_comp_of_isIso] at hker
  have hgen : ∀ {X : Scheme.{u}} [IsAffine X] (I : Ideal Γ(X, ⊤)), I ^ 2 = ⊥ →
      Scheme.IdealSheafData.ofIdealTop I ^ 2 = ⊥ := fun I hI => by
    rw [← Scheme.IdealSheafData.equivOfIsAffine_symm_apply, ← map_pow, hI]
    exact map_zero _
  rw [hker]
  exact hgen (X := (BigFppfOver.toScheme B S hS).obj W) _ h2

/-- **A universal first-order thickening with representable affine ambient, read in the site.**
Let `x : Z ⟶ X` be a morphism from the algebraic space of an object `Z` of the big fppf site of
`S`, with a universal first-order thickening `t` (Stacks 0607) whose ambient space is isomorphic
to the algebraic space of an affine object `W`. Then there are `j : Z ⟶ W` and `y : W ⟶ X` with
`j` a first-order thickening of schemes, `j ≫ y = x`, and the range of `yoneda.map j` a universal
first-order thickening of `Z` over `X` with structure morphism `y`. -/
theorem exists_universalThickening_range_yoneda_map_of_ambientIso {S : Scheme.{u}}
    {hS : B.Contains S} {Z₁ : BigFppfOver B S hS} {X : AlgebraicSpaces B S hS}
    {x : yoneda.obj Z₁ ⟶ X.1}
    (t : UniversalFirstOrderThickening B S hS (ObjectProperty.homMk x : schemeSpace Z₁ ⟶ X))
    {W : BigFppfOver B S hS} (eA : t.ambient.obj ≅ yoneda.obj W)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj W)] :
    ∃ (j : Z₁ ⟶ W) (y : yoneda.obj W ⟶ X.1),
      Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map j) ∧
        yoneda.map j ≫ y = x ∧
        IsUniversalFirstOrderThickening B S hS (Subfunctor.range (yoneda.map j))
          (ObjectProperty.homMk y : schemeSpace W ⟶ X) := by
  let sI : yoneda.obj Z₁ ≅ t.sub.toFunctor := t.sourceIso
  have hsI : sI.hom ≫ t.sub.ι ≫ t.toBase.hom = x := t.sourceIso_ι_toBase
  obtain ⟨j, hj⟩ := yoneda.map_surjective (sI.hom ≫ t.sub.ι ≫ eA.hom)
  have : Mono (yoneda.map j) := by
    rw [hj]
    have h₁ : Mono t.sub.ι := inferInstance
    have h₂ : Mono eA.hom :=
      ⟨fun _ _ w => by simpa using congrArg (· ≫ eA.inv) w⟩
    have h₃ : Mono sI.hom :=
      ⟨fun _ _ w => by simpa using congrArg (· ≫ sI.inv) w⟩
    have : Mono (t.sub.ι ≫ eA.hom) := mono_comp _ _
    exact mono_comp _ _
  let y : yoneda.obj W ⟶ X.1 := eA.inv ≫ t.toBase.hom
  have hjy : yoneda.map j ≫ y = x := by
    refine Eq.trans ?_ hsI
    rw [hj]
    simp only [y, Category.assoc, Iso.hom_inv_id_assoc]
  let g : schemeSpace W ⟶ t.ambient := ObjectProperty.homMk eA.inv
  have hg : IsEtale B S hS g.hom := isEtale_of_isIso _ _ _ eA.inv
  let a : (Subfunctor.range (yoneda.map j)).toFunctor ⟶ t.sub.toFunctor :=
    inv (Subfunctor.toRange (yoneda.map j)) ≫ sI.hom
  have : IsIso a := by dsimp only [a]; infer_instance
  have hsq : IsPullback a (Subfunctor.range (yoneda.map j)).ι t.sub.ι eA.inv := by
    refine IsPullback.of_horiz_isIso ⟨?_⟩
    rw [← cancel_epi (Subfunctor.toRange (yoneda.map j)), Subfunctor.toRange_ι_assoc]
    simp [a, hj]
  have huniv := IsUniversalFirstOrderThickening.etalePullback B S hS
    t.sub t.toBase t.isUniversal g hg (Subfunctor.range (yoneda.map j)) a hsq
  have hgy : g ≫ t.toBase = (ObjectProperty.homMk y : schemeSpace W ⟶ X) :=
    ObjectProperty.hom_ext _ rfl
  rw [hgy] at huniv
  exact ⟨j, y, isFirstOrderThickening_scheme_of_range_yoneda_map j huniv.firstOrder, hjy, huniv⟩

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Stack.FiniteHilbert

/-- **The universal first-order thickening of a cover over a deformation of its target, as an
affine object of the site.** Let `i : U ⟶ U'` be a first-order thickening of objects of the big
fppf site of `S` with `U` affine, `X'` an algebraic space over `U'`, `q : Z ⟶ U` finite locally
free of rank `d`, and `f : Z ⟶ U ×_{U'} X'` an unramified morphism into the special fibre. Then
the morphism `x : Z ⟶ X'` that `f` names over `U'` has a universal first-order thickening
(**Stacks 0606**) whose ambient space is represented by an affine object `W` of the big fppf site
of `U'`: there are `j : Z ⟶ W` and `y : W ⟶ X'` with `j` a first-order thickening of schemes,
`j ≫ y = x`, and the range of `yoneda.map j` a universal first-order thickening of `Z` over `X'`
with structure morphism `y`. -/
theorem exists_universalThickening_scheme_of_coverDeformationData {B : BigFppfSite.{u}}
    {S : Scheme.{u}} {hS : B.Contains S} {U U' : BigFppfOver B S hS} (i : U ⟶ U')
    {X' : (BigFppfOver B U'.left.1 U'.left.2)ᵒᵖ ⥤ Type u}
    (hX' : IsAlgebraicSpace B U'.left.1 U'.left.2 X') {Z : BigFppfOver B S hS} (q : Z ⟶ U)
    (f : yoneda.obj (Over.mk q.left : BigFppfOver B U.left.1 U.left.2) ⟶
      (OverShriek.relocalizeRestrict i.left).obj X')
    (hunr : Space.IsUnramified B U.left.1 U.left.2 f)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (hi : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map i))
    {d : ℕ} (hq : Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      ((BigFppfOver.toScheme B S hS).map q) d) :
    ∃ (W : BigFppfOver B U'.left.1 U'.left.2)
      (j : (Over.map i.left).obj (Over.mk q.left : BigFppfOver B U.left.1 U.left.2) ⟶ W)
      (y : yoneda.obj W ⟶ X'),
      Stacks.Thickenings.IsFirstOrderThickening
          ((BigFppfOver.toScheme B U'.left.1 U'.left.2).map j) ∧
        yoneda.map j ≫ y = yonedaEquiv.symm
          (show X'.obj (op ((Over.map i.left).obj (Over.mk q.left))) from
            yonedaEquiv (F := (OverShriek.relocalizeRestrict i.left).obj X') f) ∧
        IsAffine ((BigFppfOver.toScheme B U'.left.1 U'.left.2).obj W) ∧
        Space.IsUniversalFirstOrderThickening B U'.left.1 U'.left.2
          (Subfunctor.range (yoneda.map j))
          (ObjectProperty.homMk y : schemeSpace W ⟶ ⟨X', hX'⟩) := by
  let P : BigFppfOver B U.left.1 U.left.2 := Over.mk q.left
  let Z₁ : BigFppfOver B U'.left.1 U'.left.2 := (Over.map i.left).obj P
  let x : yoneda.obj Z₁ ⟶ X' := yonedaEquiv.symm (show X'.obj (op Z₁) from
    yonedaEquiv (F := (OverShriek.relocalizeRestrict i.left).obj X') f)
  have := hi.1
  have : Mono i.left := B.inclusion.mono_of_mono_map (inferInstanceAs
    (Mono ((BigFppfOver.toScheme B S hS).map i)))
  have hfFU : Space.FormallyUnramified f :=
    ((Space.isUnramified_iff_isLocallyOfFiniteType_and_formallyUnramified B U.left.1 U.left.2
      (isAlgebraicSpace_yoneda B U.left.1 U.left.2 P)
      (isAlgebraicSpace_relocalizeRestrict B U.left.1 U'.left.1 U.left.2 U'.left.2 i.left X' hX')
      f).1 hunr).2
  have hxFU : Space.FormallyUnramified x :=
    Space.formallyUnramified_yonedaEquiv_symm_of_relocalizeRestrict i.left X' P f hfFU
  obtain ⟨t⟩ := Space.nonempty_universalFirstOrderThickening B U'.left.1 U'.left.2
    (ObjectProperty.homMk x : schemeSpace Z₁ ⟶ ⟨X', hX'⟩) hxFU
  have hZ : IsAffine ((BigFppfOver.toScheme B U'.left.1 U'.left.2).obj Z₁) := by
    have : IsAffine ((BigFppfOver.toScheme B S hS).obj U) := hU
    have := hq.toIsAffineHom
    exact isAffine_of_isAffineHom ((BigFppfOver.toScheme B S hS).map q)
  obtain ⟨W, hW, ⟨eA⟩⟩ := Space.isAffineSpace_of_isFirstOrderThickening B U'.left.1 U'.left.2
    t.isUniversal.firstOrder ⟨Z₁, hZ, ⟨t.sourceIso.symm⟩⟩
  have := hW
  obtain ⟨j, y, hj, hjy, huniv⟩ :=
    Space.exists_universalThickening_range_yoneda_map_of_ambientIso t eA
  exact ⟨W, j, y, hj, hjy, hW, huniv⟩

end AlgebraicGeometry.Stack.FiniteHilbert

end
