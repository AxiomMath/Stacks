module

public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedFibreProducts
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactQuasiSeparatedStackAbsolute
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversalHomeomorphismAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.PresheafFibredCategoryTwoFibreProduct
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsTopologyRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactStack
public import StacksFrontier.AlgebraicGeometry.Stacks.CancelTwoFibreProductAlgebraicStack

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An algebraic space is quasi-compact as soon as the algebraic stack it defines is. -/
theorem isQuasiCompactSpace_of_isQuasiCompactStack_fibredCategory
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (h𝒰 : IsAlgebraicStack.{u, w} B S hS (fibredCategory B S hS F).val)
    (h : IsQuasiCompactStack.{u, w} B S hS (fibredCategory B S hS F) h𝒰) :
    Space.IsQuasiCompactSpace B S hS F := by
  let : TopologicalSpace (Space.points B S hS F) := Space.pointTopology B S hS F
  let : TopologicalSpace
      (points B S hS (fibredCategory B S hS F).val (fibredCategory B S hS F).property) :=
    pointTopology B S hS (fibredCategory B S hS F)
  let : CompactSpace
      (points B S hS (fibredCategory B S hS F).val (fibredCategory B S hS F).property) := h
  have hhom := isHomeomorph_spacePointMap_representing B S hS F hF (fibredCategory B S hS F)
    (StacksRepresentableCFG.EquivalenceOver.refl _)
  have : CompactSpace (Space.points B S hS F) := (hhom.homeomorph _).symm.compactSpace
  exact (Space.isQuasiCompactSpace_iff_compactSpace_points B S hS F hF).2 this

/-- Quasi-compactness of algebraic stacks passes along a 2-fibre product of categories fibred in
groupoids: two 2-fibre products of one cospan have homeomorphic spaces of points. -/
theorem compactSpace_points_of_isTwoFibreProduct
    {𝒵 𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    {g : 𝒵 ⟶ 𝒴} {f : 𝒳 ⟶ 𝒴} (P Q : Bicategory.TwoCommSq g f)
    (hP : Bicategory.IsTwoFibreProduct P) (hQ : Bicategory.IsTwoFibreProduct Q)
    (h : @CompactSpace _ (pointTopology B S hS P.pt)) :
    @CompactSpace _ (pointTopology B S hS Q.pt) := by
  let := pointTopology B S hS P.pt
  let := pointTopology B S hS Q.pt
  let a := Quotient.out (hP.from Q)
  exact ((isHomeomorph_pointsMap_of_isEquivalence B S hS Q.pt P.pt a.hom.hom
    (Bicategory.isEquivalence_of_isTwoFibreProduct hQ hP a)).homeomorph _).symm.compactSpace

/-- A universal homeomorphism of algebraic stacks over `S` is surjective on points after every
base change, in particular its base change along `g` is a homeomorphism, so the source of that
base change is quasi-compact as soon as its target is. -/
theorem isQuasiCompactStack_fst_of_universalHomeomorphism
    {𝒳 𝒴 𝒵 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : AlgebraicStacks.UniversalHomeomorphism B S hS f) (g : 𝒵 ⟶ 𝒴)
    (h𝒵 : IsQuasiCompactStack.{u, w} B S hS 𝒵.val 𝒵.property) :
    IsQuasiCompactStack.{u, w} B S hS (twoFibreProductSquareAlgebraicStacks B S hS g f).pt.val
      (twoFibreProductSquareAlgebraicStacks B S hS g f).pt.property := by
  let := pointTopology B S hS (twoFibreProductSquareAlgebraicStacks B S hS g f).pt.val
  let := pointTopology B S hS 𝒵.val
  let : CompactSpace (points B S hS 𝒵.val.val 𝒵.val.property) := h𝒵
  exact ((hf 𝒵 g).homeomorph _).symm.compactSpace

variable (hZ : B.Contains (⊤_ Scheme.{u}))

/-- **The fibre product of two affine schemes over the target of a universal homeomorphism out of
a quasi-separated algebraic stack is quasi-compact.** Let `f : 𝒳 ⟶ M` be a universal
homeomorphism from an algebraic stack, quasi-separated in the absolute sense of Stacks 050D
part (8), to an algebraic space, and let `U ⟶ M ⟵ V` be morphisms from affine objects of the site
with fibre product represented by `W`. Then `W` is quasi-compact.

Write `𝒳_U = U ×_M 𝒳` and `𝒳_V = V ×_M 𝒳`. Both are quasi-compact, being homeomorphic on points to
`U` and `V`, so their projections to the quasi-separated `𝒳` are quasi-compact (Stacks 075S
part (1)) and `𝒳_U ×_𝒳 𝒳_V` is quasi-compact. By the pasting law and the cancellation of Stacks
02XD that stack is also `(U ×_M V) ×_V 𝒳_V`, whose projection to `U ×_M V` is a base change of the
surjective `𝒳_V ⟶ V`; so `U ×_M V` is quasi-compact, and so is the algebraic space `W` representing
it (Stacks 04SD). -/
theorem compactSpace_of_isPullback_of_universalHomeomorphism
    {𝒳 : AlgebraicStacks.{u, w} B S hS} {M : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hM : IsAlgebraicSpace B S hS M) (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS M hM)
    (hf : AlgebraicStacks.UniversalHomeomorphism B S hS f)
    (h𝒳 : AlgebraicStacks.IsAbsolutelyQuasiSeparated.{u, w} B S hS hZ 𝒳)
    {U V W : BigFppfOver B S hS} (a : yoneda.obj U ⟶ M) (b : yoneda.obj V ⟶ M)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    {p : yoneda.obj W ⟶ yoneda.obj U} {q : yoneda.obj W ⟶ yoneda.obj V}
    (hpb : IsPullback p q a b) :
    CompactSpace ((BigFppfOver.toScheme B S hS).obj W) := by
  let 𝓤 := algebraicSpaceStack.{u, w} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)
  let 𝓥 := algebraicSpaceStack.{u, w} B S hS (yoneda.obj V) (isAlgebraicSpace_yoneda B S hS V)
  let u : 𝓤 ⟶ algebraicSpaceStack.{u, w} B S hS M hM :=
    Bicategory.InducedBicategory.mkHom (associatedMap B S hS a).1
  let v : 𝓥 ⟶ algebraicSpaceStack.{u, w} B S hS M hM :=
    Bicategory.InducedBicategory.mkHom (associatedMap B S hS b).1
  have h𝓤 : IsQuasiCompactStack.{u, w} B S hS 𝓤.val 𝓤.property :=
    isQuasiCompactStack_fibredCategory B S hS _ (isAlgebraicSpace_yoneda B S hS U)
      (Space.isQuasiCompactSpace_yoneda_obj B S hS inferInstance) _
  have h𝓥 : IsQuasiCompactStack.{u, w} B S hS 𝓥.val 𝓥.property :=
    isQuasiCompactStack_fibredCategory B S hS _ (isAlgebraicSpace_yoneda B S hS V)
      (Space.isQuasiCompactSpace_yoneda_obj B S hS inferInstance) _
  set C := twoFibreProductSquareAlgebraicStacks B S hS u f with hCdef
  set A := twoFibreProductSquareAlgebraicStacks B S hS v f with hAdef
  have hC : IsQuasiCompactStack.{u, w} B S hS C.pt.val C.pt.property :=
    isQuasiCompactStack_fst_of_universalHomeomorphism B S hS f hf u h𝓤
  have hA : IsQuasiCompactStack.{u, w} B S hS A.pt.val A.pt.property :=
    isQuasiCompactStack_fst_of_universalHomeomorphism B S hS f hf v h𝓥
  have hAsurj : IsSurjective B S hS A.fst := by
    let := pointTopology B S hS A.pt.val
    let := pointTopology B S hS 𝓥.val
    exact (hf 𝓥 v).surjective
  have hAqc : IsQuasiCompactMorphism.{u, w} B S hS A.snd :=
    isQuasiCompactMorphism_of_isQuasiCompactStack_absolute B S hS hZ A.snd hA h𝒳
  set R := twoFibreProductSquareAlgebraicStacks B S hS C.snd A.snd with hRdef
  have hR : IsQuasiCompactStack.{u, w} B S hS R.pt.val R.pt.property := hAqc C.pt C.snd hC
  have hpaste : Bicategory.IsTwoFibreProduct (C.paste R) :=
    Bicategory.isTwoFibreProduct_paste
      (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS u f)
      (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS C.snd A.snd)
  have hK := isTwoFibreProduct_cancelSndSquareAlgebraicStacks B S hS u v A.fst (A.snd ≫ f)
    A.iso
  have hP : IsQuasiCompactStack.{u, w} B S hS
      (cancelSndSquareAlgebraicStacks B S hS u v A.fst (A.snd ≫ f) A.iso).pt.val
      (cancelSndSquareAlgebraicStacks B S hS u v A.fst (A.snd ≫ f) A.iso).pt.property :=
    isQuasiCompactStack_of_isTwoFibreProduct B S hS hpaste hK hR
  set W' := twoFibreProductSquareAlgebraicStacks B S hS u v with hW'def
  set Pt := twoFibreProductSquareAlgebraicStacks B S hS W'.snd A.fst with hPtdef
  have hPtsurj : IsSurjective B S hS Pt.fst :=
    isSurjective_of_isTwoFibreProduct B S hS Pt.swap
      (Bicategory.isTwoFibreProduct_swap
        (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS W'.snd A.fst)) hAsurj
  have hW' : IsQuasiCompactStack.{u, w} B S hS W'.pt.val W'.pt.property :=
    isQuasiCompactStack_of_isSurjective B S hS Pt.fst hP hPtsurj
  have hQ := isTwoFibreProduct_fibredCategorySquare (B := B) (S := S) (hS := hS) hpb
  have hcpt := compactSpace_points_of_isTwoFibreProduct B S hS
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} u.hom v.hom)
    (fibredCategorySquare (B := B) (S := S) (hS := hS) hpb.w)
    (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      u.hom v.hom) hQ hW'
  have hWqc := isQuasiCompactSpace_of_isQuasiCompactStack_fibredCategory B S hS (yoneda.obj W)
    (isAlgebraicSpace_yoneda B S hS W)
    (isAlgebraicStack_fibredCategory.{u, w} B S hS _ (isAlgebraicSpace_yoneda B S hS W)) hcpt
  exact Space.compactSpace_of_isQuasiCompactSpace_yoneda_obj B S hS hWqc

/-- **The target of a universal homeomorphism out of a quasi-separated algebraic stack is
quasi-separated.** Let `f : 𝒳 ⟶ M` be a universal homeomorphism (Stacks 0CI7) from an algebraic
stack over `S` to an algebraic space over `S`. If `𝒳` is quasi-separated (Stacks 050D part (8)),
then `M` is quasi-separated (Stacks 03BS part (3)).

By Stacks 0AHR it suffices that the fibre product of two affine schemes over `M` is
quasi-compact, which is
`AlgebraicGeometry.Stack.compactSpace_of_isPullback_of_universalHomeomorphism`. -/
theorem isAbsolutelyQuasiSeparated_of_universalHomeomorphism
    {𝒳 : AlgebraicStacks.{u, w} B S hS} {M : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hM : IsAlgebraicSpace B S hS M) (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS M hM)
    (hf : AlgebraicStacks.UniversalHomeomorphism B S hS f)
    (h𝒳 : AlgebraicStacks.IsAbsolutelyQuasiSeparated.{u, w} B S hS hZ 𝒳) :
    Space.IsAbsolutelyQuasiSeparated B S hS hZ M := by
  rw [Space.isAbsolutelyQuasiSeparated_iff_compactSpace_pullback_affine B S hS hZ M hM]
  intro U V a b hU hV
  have hrep := hM.diagonal_representable.of_diag a
  have hpb := hrep.isPullback' b
  exact ⟨hrep.pullback b,
    compactSpace_of_isPullback_of_universalHomeomorphism B S hS hZ hM f hf h𝒳 a b hU hV hpb,
    ⟨hpb.isoPullback⟩⟩

end AlgebraicGeometry.Stack

end
