module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringRestrictionCoproduct
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringSieveStepOne
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.AbstractGroupQuotientStackConstantData
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.TorsorStackUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.TorsorDescent.GlueingTorsors
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedFppfCovering
public import StacksFrontier.CategoryTheory.Sites.Stack.StackBridge.ToSieve

/-!
# Existence of the glued fppf torsor

Let `{Sᵢ ⟶ S}` be a chosen covering family of the big fppf site of `S`, let `G` be a group
algebraic space over `S` and let `Gᵢ` be its base changes. Stacks 04U1 asserts that a descent
datum consisting of an fppf `Gᵢ`-torsor `Xᵢ` over each `Sᵢ` together with transition isomorphisms
over the overlaps is effective: there is an fppf `G`-torsor `X` over `S` whose base change to each
`Sᵢ` is isomorphic to `Xᵢ`, recovering the transition isomorphisms.

This file proves that. The companion file
`StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.TorsorDescent.GlueingTorsors` carries the
unconditional statement that a glued object, once supplied, is an fppf torsor.

## Main results

* `AlgebraicGeometry.isAlgebraicSpace_of_isCovering_of_size_le`: Stacks 04SK with its hypothesis
  on the coproduct of the restrictions discharged from a uniform size bound on their atlases by
  Stacks 02WQ.
* `AlgebraicGeometry.Space.isPullback_prod_fst_snd_of_isTerminal`,
  `AlgebraicGeometry.Space.prodIsoPullbackLeftOfIsTerminal` and
  `AlgebraicGeometry.Space.isAlgebraicSpace_prod_left_of_iso`: over a terminal base a base change
  is a product, so the restrictions of an object in the sense of Stacks 04SK are its base
  changes in the sense of Stacks 04TY.
* `AlgebraicGeometry.Space.isFppfCovering_yoneda_map_of_isCovering`: a chosen covering family of
  the terminal object of the site is an fppf covering of algebraic spaces.
* `AlgebraicGeometry.Space.overlapComparison`: the canonical identification of the two base
  changes of one object to an overlap.
* `AlgebraicGeometry.Space.exists_isFppfTorsor_of_descentDatum`: **Stacks 04U1**, effectivity of
  a descent datum of fppf torsors along a covering of `S`.

## Implementation notes

The datum of the source — the torsors `Xᵢ`, and the equivariant transition isomorphisms `φᵢⱼ`
satisfying the cocycle condition over the triple overlaps — is a descent datum, in the sense of
Stacks 026B, for the functor `p : G-Torsors ⥤ (Sch/S)_fppf` of Stacks 04UR at `B = S`
(`AlgebraicGeometry.Space.FppfTorsors.projection`): the objects of that category over `Sᵢ` are
the fppf `Gᵢ`-torsors over `Sᵢ`, and its morphisms over an identity are the equivariant
isomorphisms. The statement is therefore written with `CategoryTheory.Functor.DescentDatum`, whose
overlaps are genuine fibre products in the site and whose cocycle condition is built in; and the
conclusion, `CategoryTheory.Functor.DescentDatum.IsEffective`, is the source's: an object over
`S`, that is an fppf `G`-torsor `X` over `S`, with isomorphisms of its restrictions to the `Sᵢ`
with the `Xᵢ` which are compatible with the `φᵢⱼ` over the overlaps.

The proof is Stacks 04US, condition (3)
(`AlgebraicGeometry.Space.FppfTorsors.hasEffectiveDescent_projection`), read along the covering
family by `CategoryTheory.Functor.DescentDatum.isEffective_of_hasEffectiveDescent`. That
condition is itself the glueing of the underlying torsors of sheaves, Stacks 04UM, followed by the
algebraicity of the glued torsor, which is where the bootstrap theorem Stacks 04S6,
condition (3), is spent.

## References

* [Stacks Project, Tag 04U1](https://stacks.math.columbia.edu/tag/04U1)
* [Stacks Project, Tag 04SK](https://stacks.math.columbia.edu/tag/04SK)
* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
* [Stacks Project, Tag 02WQ](https://stacks.math.columbia.edu/tag/02WQ)
* [Stacks Project, Tag 04TY](https://stacks.math.columbia.edu/tag/04TY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Cardinal

universe u w

namespace AlgebraicGeometry

variable {𝒞 : BigFppfSite.{u}} {S : Scheme.{u}} {hS : 𝒞.Contains S}

/-! ### Stacks 04SK with the coproduct of the restrictions discharged by a size bound -/

/-- **Stacks 04SK with its coproduct hypothesis discharged by a size bound.**

`AlgebraicGeometry.isAlgebraicSpace_of_isCovering` asks for the algebraicity of the coproduct `G`
of the restrictions `h_{S i} × F` as a hypothesis, and that is what the closing, purely
set-theoretic paragraph of Stacks 04U1 supplies. This statement composes the two: the coproduct
is handed to `AlgebraicGeometry.isAlgebraicSpace_coproduct_of_size_le` — Stacks 02WQ under a
uniform size bound on the atlases — so what remains to be provided is an atlas `U i` of each
restriction together with the bound `size (U i) ≤ μ` and the bound `#K ≤ μ` on an index type of
the working universe in bijection with the index type of the covering. -/
theorem isAlgebraicSpace_of_isCovering_of_size_le
    {F : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology 𝒞 S hS) F)
    (E : PreZeroHypercover.{u + 1} (Over.mk (𝟙 (𝒞.obj hS))))
    (hE : BigFppfOver.IsCovering 𝒞 S hS ⟨Over.mk (𝟙 (𝒞.obj hS)), E⟩)
    (hFi : ∀ i : E.I₀, IsAlgebraicSpace 𝒞 S hS (yoneda.obj (E.X i) ⨯ F))
    {Gsh : Sheaf (BigFppfOver.topology 𝒞 S hS) (Type u)}
    (inj : ∀ i : E.I₀, (⟨yoneda.obj (E.X i) ⨯ F, (hFi i).isSheaf⟩ :
      Sheaf (BigFppfOver.topology 𝒞 S hS) (Type u)) ⟶ Gsh)
    (hcoprod : IsColimit (Cofan.mk Gsh inj))
    (U : E.I₀ → BigFppfOver 𝒞 S hS)
    (a : ∀ i, yoneda.obj (U i) ⟶ yoneda.obj (E.X i) ⨯ F)
    (hsurj : ∀ i, (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme 𝒞 S hS))) (a i))
    (hetale : ∀ i, (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme 𝒞 S hS))) (a i))
    {K : Type u} (eK : K ≃ E.I₀) {μ : Cardinal.{u}}
    (hℵ : ℵ₀ ≤ μ) (hμ : μ < 𝒞.cutoff) (hK : #K ≤ μ)
    (hsize : ∀ i, ((BigFppfOver.toScheme 𝒞 S hS).obj (U i)).size ≤ μ) :
    IsAlgebraicSpace 𝒞 S hS F :=
  isAlgebraicSpace_of_isCovering hF E hE hFi inj hcoprod
    (isAlgebraicSpace_coproduct_of_size_le 𝒞 S hS _ hFi Gsh inj hcoprod U a hsurj hetale
      eK hℵ hμ hK hsize)

namespace Space

/-! ### Base change over a terminal base -/

/-- **Over a terminal base, a base change is a product.** For `X` over a terminal presheaf `B`
and any `g : B' ⟶ B`, the total space of the base change of `X` along `g` is the product of the
total space of `X` with `B'`: both structure morphisms are the unique ones to `B`, so the product
cone is a pullback square by `CategoryTheory.IsPullback.of_is_product'`. -/
theorem isPullback_prod_fst_snd_of_isTerminal
    {B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u} (hB : IsTerminal B) (X : Over B)
    {B' : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u} (g : B' ⟶ B) :
    IsPullback (prod.fst : X.left ⨯ B' ⟶ X.left) (prod.snd : X.left ⨯ B' ⟶ B') X.hom g := by
  have h₁ : X.hom = hB.from X.left := hB.hom_ext _ _
  have h₂ : g = hB.from B' := hB.hom_ext _ _
  rw [h₁, h₂]
  exact IsPullback.of_is_product' (prodIsProd _ _) hB

/-- The restriction `B' × X` of an object `X` over a terminal presheaf `B`, in the form Stacks
04SK reads it, is the total space of the base change of `X` along `g : B' ⟶ B`. -/
def prodIsoPullbackLeftOfIsTerminal
    {B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u} (hB : IsTerminal B) (X : Over B)
    {B' : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u} (g : B' ⟶ B) :
    B' ⨯ X.left ≅ ((Over.pullback g).obj X).left :=
  (prod.braiding B' X.left).trans (isPullback_prod_fst_snd_of_isTerminal hB X g).isoPullback

/-- **The restrictions of the glued object to the members of the covering are algebraic spaces.**
If `X` over a terminal base `B` has its base change along `g : B' ⟶ B` isomorphic, over `B'`, to
an algebraic space, then the restriction `B' × X` which Stacks 04SK takes as its hypothesis is an
algebraic space. -/
theorem isAlgebraicSpace_prod_left_of_iso
    {B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u} (hB : IsTerminal B) (X : Over B)
    {B' : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u} (g : B' ⟶ B) (Y : Over B')
    (e : (Over.pullback g).obj X ≅ Y) (hY : IsAlgebraicSpace 𝒞 S hS Y.left) :
    IsAlgebraicSpace 𝒞 S hS (B' ⨯ X.left) :=
  isAlgebraicSpace_of_iso 𝒞 S hS
    (((prodIsoPullbackLeftOfIsTerminal hB X g).trans ((Over.forget B').mapIso e)).symm) hY

/-! ### A chosen covering of the base is an fppf covering of algebraic spaces -/

/-- **A chosen covering family of the terminal object of the big fppf site of `S` is an fppf
covering of algebraic spaces over `S`.** This is the bridge between the two renderings of "fppf
covering of the base" which this development carries: `AlgebraicGeometry.BigFppfOver.IsCovering`,
a membership condition on the underlying family of schemes, which Stacks 04SK consumes; and
`AlgebraicGeometry.Space.IsFppfCovering`, a condition on a family of morphisms of presheaves,
which the torsor conditions of Stacks 04TY are local for.

The geometric content of the first is unpacked by
`AlgebraicGeometry.BigFppfSite.jointlySurjective_flat_locallyOfFinitePresentation_of_isCovering`
and fed to `AlgebraicGeometry.Space.isFppfCovering_yoneda_map`. -/
theorem isFppfCovering_yoneda_map_of_isCovering
    (E : PreZeroHypercover.{u + 1} (Over.mk (𝟙 (𝒞.obj hS)) : BigFppfOver 𝒞 S hS))
    (hE : BigFppfOver.IsCovering 𝒞 S hS ⟨Over.mk (𝟙 (𝒞.obj hS)), E⟩) :
    IsFppfCovering 𝒞 S hS (fun i => yoneda.obj (E.X i)) (fun i => yoneda.map (E.f i)) := by
  obtain ⟨hsurj, hgeom⟩ :=
    BigFppfSite.jointlySurjective_flat_locallyOfFinitePresentation_of_isCovering 𝒞 hE
  refine isFppfCovering_yoneda_map 𝒞 S hS E.X E.f (fun i => (hgeom i).1)
    (fun i => (hgeom i).2) fun x => ?_
  obtain ⟨i, y, hy⟩ := hsurj x
  exact ⟨i, y, hy⟩

/-! ### The descent datum of a single object -/

/-- The base `S` itself, as the presheaf represented by the terminal object of the big fppf site
of `S`. This is the base over which Stacks 04U1 glues, and it is terminal by
`AlgebraicGeometry.Space.isTerminal_yoneda_obj_base`. -/
@[reducible] alias baseYoneda := AlgebraicGeometry.Space.baseS

/-- **The canonical comparison of the two base changes of one object to an overlap.** The
restriction of `X` to `Bᵢ` and then to `Bᵢ ×_B Bⱼ`, and its restriction to `Bⱼ` and then to
`Bᵢ ×_B Bⱼ`, are restrictions of `X` along the two equal composites `Bᵢ ×_B Bⱼ ⟶ B`, so they are
canonically identified. This is the isomorphism of which the transition isomorphism `φ i j` of a
descent datum coming from `X` is the conjugate. -/
def overlapComparison {B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u} (X : Over B)
    {Bi Bj : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u} (fi : Bi ⟶ B) (fj : Bj ⟶ B) :
    (Over.pullback (pullback.fst fi fj)).obj ((Over.pullback fi).obj X) ≅
      (Over.pullback (pullback.snd fi fj)).obj ((Over.pullback fj).obj X) :=
  ((Over.pullbackComp (pullback.fst fi fj) fi).app X).symm ≪≫
    eqToIso (congrArg (fun k => (Over.pullback k).obj X)
      (pullback.condition (f := fi) (g := fj))) ≪≫
    (Over.pullbackComp (pullback.snd fi fj) fj).app X

/-! ### Stacks 04U1 -/

variable (𝒞 S hS) in
/-- **Stacks 04U1.** Let `{f i : Sᵢ ⟶ S}` be a covering family of the big fppf site of `S` and let
`G` be a group algebraic space over `S`. A descent datum `D` of fppf torsors along that family —
for each `i` an fppf torsor `D.x i` over `Sᵢ` under the base change `Gᵢ` of `G`, and for each
`i, j` an equivariant isomorphism `D.φ i j` between the restrictions of `D.x i` and of `D.x j`
to `Sᵢ ×_S Sⱼ`, satisfying the cocycle condition over every `Sᵢ ×_S Sⱼ ×_S Sₖ` — is effective:
there is an fppf `G`-torsor `X` over `S` whose restriction to each `Sᵢ` is isomorphic to `D.x i`,
compatibly with the `D.φ i j`.

The bootstrap theorem Stacks 04S6, condition (3), is used only to see that the glued torsor of
sheaves is an algebraic space; the glueing is Stacks 04UM and the torsor conditions are carried
along by it. -/
@[stacks 04U1]
theorem exists_isFppfTorsor_of_descentDatum
    (G : GroupAlgebraicSpace 𝒞 S hS (baseYoneda 𝒞 S hS)
      (isAlgebraicSpace_yoneda 𝒞 S hS (Over.mk (𝟙 (𝒞.obj hS)))))
    {I : Type w} (V : I → BigFppfOver 𝒞 S hS) (f : ∀ i, V i ⟶ Over.mk (𝟙 (𝒞.obj hS)))
    (hf : Sieve.ofArrows V f ∈ BigFppfOver.topology 𝒞 S hS (Over.mk (𝟙 (𝒞.obj hS))))
    (Vij : I → I → BigFppfOver 𝒞 S hS)
    (pr₁ : ∀ i j, Vij i j ⟶ V i) (pr₂ : ∀ i j, Vij i j ⟶ V j)
    (hVij : ∀ i j, IsPullback (pr₁ i j) (pr₂ i j) (f i) (f j))
    (Vijk : I → I → I → BigFppfOver 𝒞 S hS)
    (s₁₂ : ∀ i j k, Vijk i j k ⟶ Vij i j) (s₂₃ : ∀ i j k, Vijk i j k ⟶ Vij j k)
    (hVijk : ∀ i j k, IsPullback (s₁₂ i j k) (s₂₃ i j k) (pr₂ i j) (pr₁ j k))
    (q₁ : ∀ i j k, Vijk i j k ⟶ V i) (q₂ : ∀ i j k, Vijk i j k ⟶ V j)
    (q₃ : ∀ i j k, Vijk i j k ⟶ V k)
    (hq₁ : ∀ i j k, q₁ i j k = s₁₂ i j k ≫ pr₁ i j)
    (hq₂ : ∀ i j k, q₂ i j k = s₁₂ i j k ≫ pr₂ i j)
    (hq₃ : ∀ i j k, q₃ i j k = s₂₃ i j k ≫ pr₂ j k)
    (D : Functor.DescentDatum
      (FppfTorsors.projection (isAlgebraicSpace_yoneda 𝒞 S hS (Over.mk (𝟙 (𝒞.obj hS)))) G)
      V f Vij pr₁ pr₂ hVij Vijk s₁₂ s₂₃ hVijk q₁ q₂ q₃ hq₁ hq₂ hq₃) :
    D.IsEffective :=
  let : (FppfTorsors.projection
      (isAlgebraicSpace_yoneda 𝒞 S hS (Over.mk (𝟙 (𝒞.obj hS)))) G).IsFibered :=
    (FppfTorsors.projection_isFiberedInGroupoids (G := G)).isFibered
  D.isEffective_of_hasEffectiveDescent (FppfTorsors.hasEffectiveDescent_projection _ G) hf

end Space

end AlgebraicGeometry

end
