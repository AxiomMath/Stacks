module

public import StacksFrontier.AlgebraicGeometry.Limits.SmallDominantIndex
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FlatImageSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.Isomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingMorphismProperties

/-!
# Stacks 0CPD: smoothness descends to the system of scheme-theoretic images

Let `B = lim_i B_i` be the limit of a directed inverse system of Noetherian algebraic spaces
over a scheme `S` with affine transition morphisms, as in Situation 0CP6, and let
`f : X ⟶ Y` be a morphism of algebraic spaces quasi-separated and of finite type over `B`.
Writing `X = lim_{i ≥ i₁} X_i` and `Y = lim_{i ≥ i₂} Y_i` for the limit descriptions by
scheme-theoretic images of Stacks 0CP9, Stacks 0CPA describes `f` as the limit of a morphism
`(f_i)_{i ≥ i₀}` of the two inverse systems. Stacks 0CPD asserts that if `f` is smooth, then so
is `f_i` for every sufficiently large `i`.

The proof combines Stacks 0CPC with Stacks 0CN2. A smooth morphism is flat and locally of
finite presentation, and `f` is quasi-compact and quasi-separated because `X` is quasi-compact
and both spaces are quasi-separated; so Stacks 0CPC applies and shows that from some stage
`i₃` on the squares formed by `f_i` and `f` are cartesian: `X = Y ×_{Y_{i₃}} X_{i₃}` and
`X_i = Y_i ×_{Y_{i₃}} X_{i₃}`. Thus `f` and the `f_i` are the base changes of the single
morphism `f_{i₃}` along the inverse system `(Y_i)_{i ≥ i₃}` with affine transition morphisms
and its limit `Y`, and `f_{i₃}` is locally of finite presentation, being locally of finite type
over the locally Noetherian algebraic space `Y_{i₃}`. Stacks 0CN2 then makes some `f_j`
smooth, and every later `f_i` is a base change of it.

## Main results

* `AlgebraicGeometry.Space.isSmooth_of_isPullback`: Stacks 03ZE read off an arbitrary
  cartesian square of algebraic spaces.
* `AlgebraicGeometry.Space.exists_isSmooth_of_isPullback_tail`: Stacks 0CN2 for an inverse
  system indexed by the stages above a fixed stage of a directed preorder, with the base
  changes given by arbitrary cartesian squares.
* `AlgebraicGeometry.Space.GoodDiagram.SystemMorphism.exists_isSmooth`: **Stacks 0CPD**.

## Implementation notes

The library's Stacks 0CN2,
`AlgebraicGeometry.Space.MorphismDescentSystem.exists_isSmooth_mapAt`, is stated for a system
indexed by a directed preorder and for the chosen fibre products. The image systems of
Stacks 0CP9 are indexed by the slice `Over (op i₀)` instead; the tail of the preorder above a
stage `m` is initial in that slice (`AlgebraicGeometry.initial_tailToOver`), so the system
`(Y_i)_{i ≥ m}` restricted to that tail is a morphism descent system with the same limit, and
cartesian squares transport smoothness to and from its chosen fibre products.

The stage `i₃` is produced with `i₀ ≤ i₃`, which is what the source's `i₃ > i₀` means for a
directed set: a strict inequality cannot be achieved when `i₀` is a largest index. The size
condition on the index type and the algebraicity of `X` and `Y` are the hypotheses under which
the library identifies `X` and `Y` with the limits of their image systems, Stacks 0CP9.

## References

* [Stacks Project, Tag 0CPD](https://stacks.math.columbia.edu/tag/0CPD)
* [Stacks Project, Tag 0CPC](https://stacks.math.columbia.edu/tag/0CPC)
* [Stacks Project, Tag 0CPA](https://stacks.math.columbia.edu/tag/0CPA)
* [Stacks Project, Tag 0CP9](https://stacks.math.columbia.edu/tag/0CP9)
* [Stacks Project, Tag 0CP6](https://stacks.math.columbia.edu/tag/0CP6)
* [Stacks Project, Tag 0CN2](https://stacks.math.columbia.edu/tag/0CN2)
* [Stacks Project, Tag 03ZE](https://stacks.math.columbia.edu/tag/03ZE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Stacks 03ZE for a cartesian square of algebraic spaces.** The base change of a smooth
morphism of algebraic spaces over `S`, along an arbitrary morphism of algebraic spaces, is
smooth. -/
theorem isSmooth_of_isPullback {W X Z Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {p : W ⟶ Z} {q : W ⟶ X} {g : Z ⟶ Y} {f : X ⟶ Y} (sq : IsPullback p q g f)
    (algW : IsAlgebraicSpace B S hS W) (algX : IsAlgebraicSpace B S hS X)
    (algZ : IsAlgebraicSpace B S hS Z) (algY : IsAlgebraicSpace B S hS Y)
    (smooth : IsSmooth B S hS f) : IsSmooth B S hS p := by
  let Wsp : AlgebraicSpaces B S hS := ⟨W, algW⟩
  let Xsp : AlgebraicSpaces B S hS := ⟨X, algX⟩
  let Zsp : AlgebraicSpaces B S hS := ⟨Z, algZ⟩
  let Ysp : AlgebraicSpaces B S hS := ⟨Y, algY⟩
  have hsq : IsPullback (ObjectProperty.homMk p : Wsp ⟶ Zsp)
      (ObjectProperty.homMk q : Wsp ⟶ Xsp) (ObjectProperty.homMk g : Zsp ⟶ Ysp)
      (ObjectProperty.homMk f : Xsp ⟶ Ysp) :=
    IsPullback.of_map_of_faithful (ObjectProperty.ι _) sq
  exact (smoothMorphismProperty B S hS).of_isPullback hsq.flip smooth

section Tail

variable {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [Nonempty I]
  [IsDirectedOrder I]

/-- **Stacks 0CN2 for a system indexed by a slice.** Let `(Y_j)` be an inverse system of
algebraic spaces over `S` indexed by the stages `j ≥ i₀` of a directed preorder, with affine
transition morphisms and limit an algebraic space `Y`, and let `f₀ : X₀ ⟶ Y_m` be a morphism
locally of finite presentation of quasi-compact quasi-separated algebraic spaces whose base
change `f : X ⟶ Y` to the limit is smooth. Then the base change of `f₀` to some later stage
`Y_j` is smooth. -/
theorem exists_isSmooth_of_isPullback_tail (small : Cardinal.mk I < B.cutoff.ord.cof)
    {i₀ m : I} (hm : i₀ ≤ m) (Ys : Over (op i₀) ⥤ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    {c : Cone Ys} (hc : IsLimit c) (algYs : ∀ j, IsAlgebraicSpace B S hS (Ys.obj j))
    (affYs : ∀ {j k : Over (op i₀)} (a : j ⟶ k), IsAffineHom B S hS (Ys.map a))
    (algY : IsAlgebraicSpace B S hS c.pt)
    (qcYm : IsQuasiCompactSpace B S hS (Ys.obj (Over.mk (homOfLE hm).op)))
    (qsYm : IsAbsolutelyQuasiSeparated B S hS hZ (Ys.obj (Over.mk (homOfLE hm).op)))
    {X₀ X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (algX₀ : IsAlgebraicSpace B S hS X₀)
    (qcX₀ : IsQuasiCompactSpace B S hS X₀) (qsX₀ : IsAbsolutelyQuasiSeparated B S hS hZ X₀)
    (f₀ : X₀ ⟶ Ys.obj (Over.mk (homOfLE hm).op))
    (fp : IsLocallyOfFinitePresentation B S hS f₀)
    {q : X ⟶ X₀} {f : X ⟶ c.pt} (sq : IsPullback q f f₀ (c.π.app (Over.mk (homOfLE hm).op)))
    (smooth : IsSmooth B S hS f) :
    ∃ (j : Over (op i₀)) (a : j ⟶ Over.mk (homOfLE hm).op),
      ∀ {X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (q' : X' ⟶ X₀) (f' : X' ⟶ Ys.obj j),
        IsPullback q' f' f₀ (Ys.map a) → IsSmooth B S hS f' := by
  classical
  let _ : Nonempty (Set.Ici m) := ⟨⟨m, le_rfl⟩⟩
  let _ := directed_tail m
  let _ := initial_tailToOver m
  let G : (Set.Ici m)ᵒᵖ ⥤ Over (op i₀) := tailToOver m ⋙ Over.map ((homOfLE hm).op)
  have hc' : IsLimit (c.whisker G) := (Functor.Initial.isLimitWhiskerEquiv G c).symm hc
  let e : limit (G ⋙ Ys) ≅ c.pt := (limit.isLimit _).conePointUniqueUpToIso hc'
  have he : ∀ j, e.hom ≫ c.π.app (G.obj j) = limit.π (G ⋙ Ys) j := fun j =>
    (limit.isLimit _).conePointUniqueUpToIso_hom_comp hc' j
  let D : MorphismDescentSystem B S hS hZ (Set.Ici m) :=
    { base := G ⋙ Ys
      indexSize := lt_of_le_of_lt (Cardinal.mk_set_le _) small
      base_isAlgebraicSpace := fun _ => algYs _
      transition_affine := fun a => affYs _
      limit_isAlgebraicSpace := isAlgebraicSpace_of_iso B S hS e.symm algY
      initial := ⟨m, le_rfl⟩
      source₀ := X₀
      target₀ := Ys.obj (Over.mk (homOfLE hm).op)
      sourceToBase := f₀
      targetToBase := 𝟙 _
      map₀ := f₀
      map₀_over := Category.comp_id _
      source₀_isAlgebraicSpace := algX₀
      target₀_isAlgebraicSpace := algYs _
      base₀_quasiCompact := qcYm
      base₀_quasiSeparated := qsYm
      source₀_quasiCompact := qcX₀
      source₀_quasiSeparated := qsX₀
      target₀_quasiCompact := qcYm
      target₀_quasiSeparated := qsYm }
  -- The base change of `f₀` to the limit of the reindexed system is a base change of `f`.
  let πm := limit.π D.base (op D.initial)
  have sq₀ : IsPullback q f D.sourceToBase (c.π.app (G.obj (op D.initial))) := sq
  have algX : IsAlgebraicSpace B S hS X :=
    isAlgebraicSpace_of_iso B S hS sq₀.isoPullback.symm
      (isAlgebraicSpace_pullback B S hS _ _ algX₀ algY (algYs _))
  have outer : IsPullback (pullback.snd πm D.sourceToBase) D.mapLimit D.map₀
      (pullback.snd πm D.targetToBase) := by
    refine IsPullback.of_bot ?_ D.mapLimit_snd.symm D.targetLimit_isPullback.flip
    convert D.sourceLimit_isPullback.flip using 2
    · exact D.mapLimit_fst
    · exact D.map₀_over
  let ψ : D.targetLimit ⟶ c.pt := pullback.fst πm D.targetToBase ≫ e.hom
  have hψ : ψ ≫ c.π.app (G.obj (op D.initial)) = pullback.snd πm D.targetToBase :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun z => pullback.fst πm D.targetToBase ≫ z) (he (op D.initial))).trans
        (pullback.condition.trans (Category.comp_id _)))
  have sqL := IsPullback.of_right' (h₂₁ := ψ) (by rwa [← hψ] at outer) sq₀
  have smoothLim : IsSmooth B S hS D.mapLimit :=
    isSmooth_of_isPullback sqL.flip D.sourceLimit_isAlgebraicSpace algX
      D.targetLimit_isAlgebraicSpace algY smooth
  -- Stacks 0CN2 gives a stage at which the base change of `f₀` is smooth.
  obtain ⟨i, hi, hsm⟩ := D.exists_isSmooth_mapAt smoothLim fp
  refine ⟨G.obj (op i), G.map (homOfLE hi).op, fun {X'} q' f' sq' => ?_⟩
  let t := D.baseAtToInitial i hi
  have sq'' : IsPullback q' f' D.sourceToBase t := sq'
  have algX' : IsAlgebraicSpace B S hS X' :=
    isAlgebraicSpace_of_iso B S hS
      (sq''.isoIsPullback _ _ (IsPullback.of_hasPullback t D.sourceToBase).flip).symm
      (D.sourceAt_isAlgebraicSpace i hi)
  let l : D.base.obj (op i) ⟶ D.targetAt i hi :=
    pullback.lift (𝟙 _) t ((Category.id_comp t).trans (Category.comp_id t).symm)
  have hl : l ≫ pullback.snd t D.targetToBase = t := pullback.lift_snd _ _ _
  have sqL' := IsPullback.of_right' (h₂₁ := l) (by rwa [← hl] at sq'') (D.isPullback_mapAt i hi)
  exact isSmooth_of_isPullback sqL'.flip algX' (D.sourceAt_isAlgebraicSpace i hi) (algYs _)
    (D.targetAt_isAlgebraicSpace i hi) hsm

end Tail

/-! ### Stacks 0CPD -/

namespace GoodDiagram.SystemMorphism

variable {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [Nonempty I]
  [IsDirectedOrder I] {D : NoetherianLimitSystem B S hS hZ I}
  {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {pX : X ⟶ D.limitCone.pt} {pY : Y ⟶ D.limitCone.pt}

/-- **Stacks 0CPD.** In Situation 0CP6, let `f : X ⟶ Y` be a morphism of algebraic spaces
quasi-separated over `B`, let `GX` and `GY` be diagrams as in Stacks 0CP8 for `X` and `Y`, and
let `(f_i)_{i ≥ i₀}` be a morphism of the inverse systems of scheme-theoretic images
`X = lim X_i` and `Y = lim Y_i` whose limit is `f`, as in Stacks 0CPA. If `f` is smooth, then
there is a stage `i₃ ≥ i₀` such that `f_i` is smooth for every `i ≥ i₃`. -/
@[stacks 0CPD]
theorem exists_isSmooth (algX : IsAlgebraicSpace B S hS X)
    (algY : IsAlgebraicSpace B S hS Y) (qsX : IsQuasiSeparated B S hS pX)
    (qsY : IsQuasiSeparated B S hS pY) (small : Cardinal.mk I < B.cutoff.ord.cof)
    {GX : GoodDiagram B S hS hZ D pX} {GY : GoodDiagram B S hS hZ D pY} {f : X ⟶ Y}
    {i₀ : I} {leX : GX.index ≤ i₀} {leY : GY.index ≤ i₀}
    (F : SystemMorphism GX GY f i₀ leX leY) (smooth : IsSmooth B S hS f) :
    ∃ i₃ : I, i₀ ≤ i₃ ∧ ∀ k : Over (op i₀), i₃ ≤ k.left.unop →
      IsSmooth B S hS (F.maps.app k) := by
  classical
  -- `f` is flat and of finite presentation.
  have qsXa : IsAbsolutelyQuasiSeparated B S hS hZ X :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated_limitCone algX small qsX
  have qsYa : IsAbsolutelyQuasiSeparated B S hS hZ Y :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated_limitCone algY small qsY
  have qcX : IsQuasiCompactSpace B S hS X :=
    isQuasiCompactSpace_source_of_isQuasiCompact B S hS
      (tailSystem_isAlgebraicSpace GX leX (Over.mk (𝟙 (op i₀))))
      (tailSystem_isQuasiCompactSpace GX leX _)
      (isQuasiCompact_tailCone_π GX leX small (Over.mk (𝟙 (op i₀))))
  have fp : IsFinitePresentation B S hS f :=
    ⟨isLocallyOfFinitePresentation_of_isSmooth B S hS smooth,
      isQuasiCompact_of_isQuasiCompactSpace B S hS hZ algY qsYa qcX f,
      isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS hZ algX qsXa f⟩
  -- Stacks 0CPC: from some stage on, the system morphism is cartesian.
  obtain ⟨i₃, h₀₃, H⟩ := exists_isFlat_isPullback algX algY qsX qsY small F
    (isFlat_of_isSmooth B S hS f smooth) fp
  let k₃ : Over (op i₀) := Over.mk (homOfLE h₀₃).op
  obtain ⟨-, sqX, -⟩ := H k₃ le_rfl
  -- The component `f_{i₃}` is locally of finite presentation.
  have ftk : IsLocallyOfFiniteType B S hS (F.maps.app k₃) :=
    isLocallyOfFiniteType_of_comp B S hS (tailSystem_isAlgebraicSpace GX leX k₃)
      (tailSystem_isAlgebraicSpace GY leY k₃) (D.system_isAlgebraicSpace _) _
      (tailBase GY leY k₃) (by
        rw [show F.maps.app k₃ ≫ tailBase GY leY k₃ = tailBase GX leX k₃ from F.over_base k₃]
        exact isLocallyOfFiniteType_tailBase GX leX k₃)
  have fpk : IsLocallyOfFinitePresentation B S hS (F.maps.app k₃) :=
    isLocallyOfFinitePresentation_of_isLocallyOfFiniteType B S hS
      (tailSystem_isAlgebraicSpace GX leX k₃) (tailSystem_isAlgebraicSpace GY leY k₃) _
      (tailSystem_isLocallyNoetherian GY leY k₃) ftk
  -- Stacks 0CN2, along the image system of `Y` above `i₃`.
  obtain ⟨j, a, Hj⟩ := exists_isSmooth_of_isPullback_tail small h₀₃ (tailSystem GY leY)
    (isLimit_tailCone GY leY algY small) (tailSystem_isAlgebraicSpace GY leY)
    (tailSystem_map_isAffineHom GY leY) algY
    (tailSystem_isQuasiCompactSpace GY leY k₃)
    (tailSystem_isAbsolutelyQuasiSeparated GY leY algY qsY small k₃)
    (tailSystem_isAlgebraicSpace GX leX k₃) (tailSystem_isQuasiCompactSpace GX leX k₃)
    (tailSystem_isAbsolutelyQuasiSeparated GX leX algX qsX small k₃) (F.maps.app k₃) fpk sqX
    smooth
  have hj : i₃ ≤ j.left.unop := leOfHom a.left.unop
  have smoothj : IsSmooth B S hS (F.maps.app j) := Hj _ _ ((H k₃ le_rfl).2.2 j a)
  -- Every later component is a base change of `f_j`.
  refine ⟨j.left.unop, leOfHom j.hom.unop, fun k hk => ?_⟩
  let b : k ⟶ j := Over.homMk (homOfLE hk).op (Subsingleton.elim _ _)
  exact isSmooth_of_isPullback ((H j hj).2.2 k b).flip (tailSystem_isAlgebraicSpace GX leX k)
    (tailSystem_isAlgebraicSpace GX leX j) (tailSystem_isAlgebraicSpace GY leY k)
    (tailSystem_isAlgebraicSpace GY leY j) smoothj

end GoodDiagram.SystemMorphism

end AlgebraicGeometry.Space

end
