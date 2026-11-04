module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitePresentationBaseChangeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatOpenPointsAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductUniversalProperty
public import StacksFrontier.AlgebraicGeometry.Stacks.UnderlyingTwoFibreProduct
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversalHomeomorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversallyInjectiveDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversallyOpenSubmersiveBaseChange
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CospanReindex
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Pasting

/-!
# Universal homeomorphisms descend along a flat cover (Stacks 0DTQ)

**Stacks 0DTQ** says that a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` is a universal
homeomorphism as soon as its base change `𝒲 ×_𝒴 𝒳 ⟶ 𝒲` is one, for some surjective, flat,
locally finitely presented 1-morphism `g : 𝒲 ⟶ 𝒴` from the stack of an algebraic space.

## Main results

* `AlgebraicGeometry.Stack.isHomeomorph_pointsMap_fst_of_isTwoFibreProduct`: being a
  homeomorphism on points is a property of the cospan and not of the chosen model of the base
  change.
* `AlgebraicGeometry.Stack.universalHomeomorphism_of_fppfCover`: **Stacks 0DTQ**.

## Implementation notes

Injectivity is **Stacks 0DTP**
(`AlgebraicGeometry.Stack.universallyInjective_of_fppfCover`), applied to the universal
injectivity the hypothesis contains. The remaining two conditions are proved over a fixed test
1-morphism `k : 𝒵 ⟶ 𝒴` from the square `C := 𝒲 ×_𝒴 𝒵`, whose projection `C.fst` to `𝒵` is the
base change of `g` and is therefore surjective (**Stacks 04XH**) as well as flat and locally of
finite presentation, hence open on points by **Stacks 06R7**. Over `C` the base change of `f`
has two descriptions,

* `D := C.pt ×_𝒲 (𝒲 ×_𝒴 𝒳)`, where the hypothesis applies directly, and
* `E := C.pt ×_𝒵 (𝒵 ×_𝒴 𝒳)`, which carries the filler of the square to be studied,

and pasting (`CategoryTheory.Bicategory.isTwoFibreProduct_pasteFst`) exhibits both as 2-fibre
products of one cospan — of `(C.snd ≫ g, f)` for `D` and of `(C.fst ≫ k, f)` for `E`, the two
cospans differing exactly by the filler `C.iso` of `C`, so that reindexing along it
(`CategoryTheory.Bicategory.isTwoFibreProduct_reindexFst`) puts them over the same one. Model
independence then moves the homeomorphism from `D.fst` to `E.fst`.

What is left is point-set: `|E.pt|` is the fibre product of `|Q.pt| → |𝒵|` and `|C.pt| → |𝒵|` by
Stacks 04XH, its projection to `|C.pt|` is a homeomorphism and its projection to `|Q.pt|` is
continuous, so the preimage along the open surjection `|C.pt| → |𝒵|` of the image of an open set
of `|Q.pt|` is open, and openness descends. Surjectivity is read off the same square. The
argument needs no scheme chart of `𝒲 ×_𝒴 𝒵`, which the source interposes because it works with
the characterisation of openness for morphisms from a scheme; here Stacks 06R7 is available for
`C.fst` itself.

## References

* [Stacks Project, Tag 04XH](https://stacks.math.columbia.edu/tag/04XH)
* [Stacks Project, Tag 06R7](https://stacks.math.columbia.edu/tag/06R7)
* [Stacks Project, Tag 0CI7](https://stacks.math.columbia.edu/tag/0CI7)
* [Stacks Project, Tag 0DTP](https://stacks.math.columbia.edu/tag/0DTP)
* [Stacks Project, Tag 0DTQ](https://stacks.math.columbia.edu/tag/0DTQ)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Openness descends along an open surjection through a fibre square.** If `φ` and `p` have a
common pullback realised by `i` and `j` with `p` an open surjection, `i` continuous and `j` open,
then `φ` is open: the preimage along `p` of the image of an open set is the `j`-image of its
`i`-preimage. -/
private theorem isOpenMap_of_openSurjectiveCover {A C D Z : Type*} [TopologicalSpace A]
    [TopologicalSpace C] [TopologicalSpace D] [TopologicalSpace Z]
    (φ : A → Z) (p : C → Z) (i : D → A) (j : D → C)
    (hcomm : ∀ d, φ (i d) = p (j d))
    (hlift : ∀ a c, φ a = p c → ∃ d, i d = a ∧ j d = c)
    (hp : Function.Surjective p) (hpopen : IsOpenMap p)
    (hi : Continuous i) (hjopen : IsOpenMap j) :
    IsOpenMap φ := by
  intro U hU
  have hpre : p ⁻¹' (φ '' U) = j '' (i ⁻¹' U) := by
    ext c
    refine ⟨fun ⟨a, ha, h⟩ => ?_, fun ⟨d, hd, hdc⟩ => hdc ▸ ⟨i d, hd, hcomm d⟩⟩
    obtain ⟨d, rfl, rfl⟩ := hlift a c h
    exact ⟨d, ha, rfl⟩
  rw [← Set.image_preimage_eq (φ '' U) hp, hpre]
  exact hpopen _ (hjopen _ (hi.isOpen_preimage U hU))

/-- **Being a homeomorphism on points is a property of the cospan, not of the model.** If the
first projection of one 2-fibre product of a cospan of algebraic stacks over `S` is a
homeomorphism on the spaces of points of Stacks 04XG and 04XL, then so is that of any other. -/
theorem isHomeomorph_pointsMap_fst_of_isTwoFibreProduct
    {𝒳 𝒴 𝒵 : AlgebraicStacks.{u, w} B S hS} {f : 𝒳 ⟶ 𝒵} {g : 𝒴 ⟶ 𝒵}
    {P Q : Bicategory.TwoCommSq f g} (hP : Bicategory.IsTwoFibreProduct P)
    (hQ : Bicategory.IsTwoFibreProduct Q)
    (h : @IsHomeomorph _ _ (pointTopology B S hS Q.pt.val) (pointTopology B S hS 𝒳.val)
      (AlgebraicStacks.pointsMap B S hS Q.fst)) :
    @IsHomeomorph _ _ (pointTopology B S hS P.pt.val) (pointTopology B S hS 𝒳.val)
      (AlgebraicStacks.pointsMap B S hS P.fst) := by
  let _ := pointTopology B S hS P.pt.val
  let _ := pointTopology B S hS Q.pt.val
  let _ := pointTopology B S hS 𝒳.val
  obtain ⟨c, -⟩ := Quotient.exists_rep (hQ.from P)
  have hproj : AlgebraicStacks.pointsMap B S hS P.fst =
      AlgebraicStacks.pointsMap B S hS Q.fst ∘ AlgebraicStacks.pointsMap B S hS c.hom :=
    (AlgebraicStacks.pointsMap_eq_of_hom₂ B S hS c.isoFst.hom).trans
      (AlgebraicStacks.pointsMap_comp B S hS c.hom Q.fst)
  exact ⟨continuous_pointsMap B S hS P.pt.val 𝒳.val P.fst.hom.hom,
    isOpenMap_pointsMap_fst_congr B S hS Q.underlying P.underlying
      (isTwoFibreProduct_underlying_algebraicStacks B S hS Q hQ)
      (isTwoFibreProduct_underlying_algebraicStacks B S hS P hP) h.isOpenMap,
    hproj ▸ h.bijective.comp (AlgebraicStacks.bijective_pointsMap_preHom B S hS hP hQ c)⟩

/-- **Stacks 0DTQ.** Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S` and let
`g : 𝒲 ⟶ 𝒴` be a surjective, flat, locally finitely presented 1-morphism from the stack of an
algebraic space. If the base change `𝒲 ×_𝒴 𝒳 ⟶ 𝒲` of `f` along `g` is a universal
homeomorphism, then so is `f`. -/
@[stacks 0DTQ]
theorem universalHomeomorphism_of_fppfCover {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hW : IsAlgebraicSpace B S hS W)
    (g : algebraicSpaceStack.{u, w} B S hS W hW ⟶ 𝒴)
    (hgSurj : IsSurjective B S hS g)
    (hgFlat : AlgebraicStacks.IsFlat B S hS g)
    (hgLfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS g)
    (hgf : UniversalHomeomorphism B S hS
      (AlgebraicStacks.twoFibreProductSquare B S hS g f).fst) :
    UniversalHomeomorphism B S hS f := by
  have hinj : UniversallyInjective B S hS f :=
    universallyInjective_of_fppfCover B S hS f W hW g hgSurj hgFlat hgLfp
      (universallyInjective_of_universalHomeomorphism B S hS hgf)
  intro 𝒵 k Q hQ
  set K := AlgebraicStacks.twoFibreProductSquare B S hS g f with hKdef
  have hK := AlgebraicStacks.isTwoFibreProduct_twoFibreProductSquare B S hS g f
  set C := AlgebraicStacks.twoFibreProductSquare B S hS k g with hCdef
  have hC := AlgebraicStacks.isTwoFibreProduct_twoFibreProductSquare B S hS k g
  set D := AlgebraicStacks.twoFibreProductSquare B S hS C.snd K.fst with hDdef
  have hD := AlgebraicStacks.isTwoFibreProduct_twoFibreProductSquare B S hS C.snd K.fst
  set E := AlgebraicStacks.twoFibreProductSquare B S hS C.fst Q.fst with hEdef
  have hE := AlgebraicStacks.isTwoFibreProduct_twoFibreProductSquare B S hS C.fst Q.fst
  let _ := pointTopology B S hS 𝒵.val
  let _ := pointTopology B S hS Q.pt.val
  let _ := pointTopology B S hS C.pt.val
  let _ := pointTopology B S hS E.pt.val
  -- the base change of the cover is an open surjection on points
  have hCsurj : Function.Surjective (AlgebraicStacks.pointsMap B S hS C.fst) := by
    intro z
    obtain ⟨y, hy⟩ := hgSurj (AlgebraicStacks.pointsMap B S hS k z)
    obtain ⟨c, hc, -⟩ :=
      AlgebraicStacks.exists_point_of_isTwoFibreProduct B S hS C hC z y hy.symm
    exact ⟨c, hc⟩
  have hCopen := AlgebraicStacks.isOpenMap_pointsMap B S hS C.fst
    (AlgebraicStacks.isFlat_baseChange B S hS g k C hC hgFlat)
    (AlgebraicStacks.isLocallyOfFinitePresentation_baseChange B S hS g k C hC hgLfp)
  -- `E` and `D` are 2-fibre products of one cospan, so the hypothesis at `D` transfers to `E`
  -- stated at the reindexed pasted square, whose apex and first projection *are* those of `E`;
  -- annotating it as `E` instead would make the elaborator pick `E` for the implicit square
  have hEpaste := isHomeomorph_pointsMap_fst_of_isTwoFibreProduct B S hS
    (Bicategory.isTwoFibreProduct_reindexFst C.iso
      (Bicategory.isTwoFibreProduct_pasteFst Q hQ E hE))
    (Bicategory.isTwoFibreProduct_pasteFst K hK D hD) (hgf C.pt C.snd D hD)
  have hEfst : @IsHomeomorph _ _ (pointTopology B S hS E.pt.val)
      (pointTopology B S hS C.pt.val) (AlgebraicStacks.pointsMap B S hS E.fst) := hEpaste
  have hcomm : ∀ e, AlgebraicStacks.pointsMap B S hS Q.fst
      (AlgebraicStacks.pointsMap B S hS E.snd e) =
      AlgebraicStacks.pointsMap B S hS C.fst (AlgebraicStacks.pointsMap B S hS E.fst e) := by
    intro e
    have h := AlgebraicStacks.pointsMap_eq_of_hom₂ B S hS E.iso.hom
    rw [AlgebraicStacks.pointsMap_comp, AlgebraicStacks.pointsMap_comp] at h
    exact (congrFun h e).symm
  refine ⟨continuous_pointsMap B S hS Q.pt.val 𝒵.val Q.fst.hom.hom, ?_, hinj 𝒵 k Q hQ, ?_⟩
  · exact isOpenMap_of_openSurjectiveCover (AlgebraicStacks.pointsMap B S hS Q.fst)
      (AlgebraicStacks.pointsMap B S hS C.fst) (AlgebraicStacks.pointsMap B S hS E.snd)
      (AlgebraicStacks.pointsMap B S hS E.fst) hcomm
      (fun a c h => (AlgebraicStacks.exists_point_of_isTwoFibreProduct B S hS E hE c a
        h.symm).imp fun _ => And.symm) hCsurj hCopen
      (continuous_pointsMap B S hS E.pt.val Q.pt.val E.snd.hom.hom) hEfst.isOpenMap
  · intro z
    obtain ⟨c, hc⟩ := hCsurj z
    obtain ⟨e, he⟩ := hEfst.surjective c
    exact ⟨AlgebraicStacks.pointsMap B S hS E.snd e, by rwa [hcomm e, he]⟩

end AlgebraicGeometry.Stack

end
