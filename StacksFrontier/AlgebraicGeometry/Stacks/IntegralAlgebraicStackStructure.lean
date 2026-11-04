module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.DenseSchematicLocusDecent
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.Properties.Reduced
public import StacksFrontier.AlgebraicGeometry.Stacks.DecentRepresentedSpace
public import StacksFrontier.AlgebraicGeometry.Stacks.DecentStackSoberInertia
public import StacksFrontier.AlgebraicGeometry.Stacks.DenseOpenGerbe
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatAlgebraicStackComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.FppfDescentIngredients
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeDecent
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeOverOpenSubscheme
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionMonomorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionPointsAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.IntegralAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.MonomorphismDeligneMumford
public import StacksFrontier.AlgebraicGeometry.Stacks.NoetherianPointsAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableDecent
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasScheme
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasSpace
public import StacksFrontier.CategoryTheory.FiberedCategory.ElementsSection

/-!
# The structure of an integral algebraic stack (Stacks 0GWC)

Let `𝒳` be an integral algebraic stack over `S` (**Stacks 0GWB**): reduced, decent, with
quasi-compact inertia projection and irreducible space of points. **Stacks 0GWC** says that
1. `|𝒳|` is sober, irreducible, and has a unique generic point;
2. there is an open substack `𝒰 ⊆ 𝒳` which is a gerbe over an integral scheme `U`.

## Main results

* `AlgebraicGeometry.Stack.stacksSober_and_exists_openSubstack_isGerbeOver_of_isIntegral`:
  **Stacks 0GWC**.
* `AlgebraicGeometry.Stack.stacksSober_irreducibleSpace_existsUnique_isGenericPoint_of_isIntegral`
  and `AlgebraicGeometry.Stack.exists_openSubstack_isGerbeOver_isIntegral`: its two parts.
* `AlgebraicGeometry.Stack.OpenSubstack.isDecent` and
  `AlgebraicGeometry.Stack.OpenSubstack.isReducedStack`: an open substack inherits decency and
  reducedness.
* `AlgebraicGeometry.Stack.isReduced_of_isGerbeOver_schemeStack`: a scheme over which a reduced
  algebraic stack is a gerbe is reduced.
* `AlgebraicGeometry.Stack.isIntegral_of_isGerbeOver_openSubstack`: a nonempty scheme over which
  an open substack of a reduced irreducible algebraic stack is a gerbe is integral.

## Implementation notes

Sobriety is `StacksSober` of Stacks 004X, the form of **Stacks 0GW9**
(`AlgebraicGeometry.Stack.AlgebraicStacks.stacksSober_points_of_isDecent`); the generic point is
`IsGenericPoint x Set.univ`. A scheme `U` over `S` in the site is read as the algebraic stack
`AlgebraicGeometry.Stack.schemeStack` of its big fppf site, and "a gerbe over `U`" is a
1-morphism to it which is `AlgebraicGeometry.Stack.AlgebraicStacks.IsGerbeOver` (**Stacks 06QC**).

The source's "small detail omitted" — that the base `U` of the gerbe is reduced — is proved
without passing through `U_red` (Stacks 050B): a smooth surjective chart of `𝒰` by a reduced
scheme, followed by the gerbe, is flat and surjective onto `U` (Stacks 06QI), and reducedness
descends along flat surjections (Stacks 06MI). The source makes `U` an integral algebraic space
first and then shrinks it to a scheme; here the shrinking to the dense open schematic locus of the
decent space (Spaces over Fields, Section 0AD3) is done first, and integrality is checked on the
scheme directly.

## References

* [Stacks Project, Tag 004X](https://stacks.math.columbia.edu/tag/004X)
* [Stacks Project, Tag 06MI](https://stacks.math.columbia.edu/tag/06MI)
* [Stacks Project, Tag 06QI](https://stacks.math.columbia.edu/tag/06QI)
* [Stacks Project, Tag 06R9](https://stacks.math.columbia.edu/tag/06R9)
* [Stacks Project, Tag 06RC](https://stacks.math.columbia.edu/tag/06RC)
* [Stacks Project, Tag 0GW3](https://stacks.math.columbia.edu/tag/0GW3)
* [Stacks Project, Tag 0GW5](https://stacks.math.columbia.edu/tag/0GW5)
* [Stacks Project, Tag 0GW9](https://stacks.math.columbia.edu/tag/0GW9)
* [Stacks Project, Tag 0GWB](https://stacks.math.columbia.edu/tag/0GWB)
* [Stacks Project, Tag 0GWC](https://stacks.math.columbia.edu/tag/0GWC)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The inclusion of an open substack is an immersion. -/
private theorem OpenSubstack.isImmersion_inclusion {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (W : OpenSubstack 𝒳) : AlgebraicStacks.IsImmersion B S hS W.inclusion :=
  ⟨W.isOpenImmersion.1, fun U y hy F hF he =>
    Space.isImmersion_of_isOpenImmersion B S hS (W.isOpenImmersion.2 U y hy F hF he)⟩

/-- **An open substack of a decent algebraic stack is decent**, by **Stacks 0GW3**: its inclusion
is representable by algebraic spaces and, being a monomorphism (**Stacks 0504**), quasi-separated.
-/
theorem OpenSubstack.isDecent {𝒳 : AlgebraicStacks.{u, w} B S hS} (W : OpenSubstack 𝒳)
    (h𝒳 : IsDecent B S hS 𝒳.val) : IsDecent B S hS W.toAlgebraicStack.val :=
  isDecent_of_representable_or_quasiSeparated B S hS W.inclusion h𝒳
    (Or.inr ⟨W.isOpenImmersion.1, AlgebraicStacks.isQuasiSeparated_of_isMonomorphism B S hS _
      (AlgebraicStacks.isMonomorphism_of_isImmersion B S hS _
        (W.isImmersion_inclusion B S hS))⟩)

/-- **An open substack of a reduced algebraic stack is reduced.** Reducedness of an algebraic
stack is tested on every smooth chart by a scheme (**Stacks 04YF**), and a smooth chart of the
open substack followed by its inclusion, which is smooth, is a smooth chart of the stack. -/
theorem OpenSubstack.isReducedStack {𝒳 : AlgebraicStacks.{u, w} B S hS} (W : OpenSubstack 𝒳)
    (h𝒳 : IsReducedStack B S hS 𝒳) : IsReducedStack B S hS W.toAlgebraicStack := by
  have hincl : AlgebraicStacks.IsSmooth B S hS W.inclusion :=
    hasPropertyOnSomeSmoothDiagram_of_hasRelativeProperty.{u, w, u} B S hS
      (fun _ _ h => Space.IsSmooth B S hS h) 𝒳.property W.inclusion.hom W.isOpenImmersion.1
      (fun U _ _ _ _ he => Space.isSmooth_of_isEtale B S hS (isAlgebraicSpace_yoneda B S hS U)
        (Space.isEtale_of_isOpenImmersion B S hS (W.isOpenImmersion.2 _ _ ‹_› _ _ he)))
  refine (exists_scheme_atlas_iff_forall_scheme B S hS (fun T : Scheme.{u} => IsReduced T)
    W.toAlgebraicStack).2 (fun V a ha => ?_)
  exact (exists_scheme_atlas_iff_forall_scheme B S hS (fun T : Scheme.{u} => IsReduced T) 𝒳).1
    h𝒳 V (a ≫ W.inclusion) (AlgebraicStacks.isSmooth_comp B S hS a W.inclusion ha hincl)

/-- **The base of a gerbe with reduced source is reduced, for a scheme base.** Let `h : 𝒰 ⟶ U`
make the reduced algebraic stack `𝒰` a gerbe over the algebraic stack of a scheme `U`. Then `U`
is reduced.

A smooth surjective chart `A ⟶ 𝒰` by a reduced scheme (**Stacks 04YF**) composed with `h` is
flat and surjective, `h` being flat by **Stacks 06QI**; on representing algebraic spaces it is a
flat surjective morphism `A ⟶ U` (**Stacks 06FM**), and reducedness descends along it
(**Stacks 06MI**). -/
theorem isReduced_of_isGerbeOver_schemeStack {𝒰 : AlgebraicStacks.{u, w} B S hS}
    {U : BigFppfOver B S hS} (h : 𝒰 ⟶ schemeStack.{u, w} B S hS U)
    (hh : AlgebraicStacks.IsGerbeOver B S hS h) (h𝒰 : IsReducedStack B S hS 𝒰) :
    IsReduced ((BigFppfOver.toScheme B S hS).obj U) := by
  obtain ⟨A, a, hasurj, hasm, hA⟩ := h𝒰
  have hhflat : AlgebraicStacks.IsFlat B S hS h :=
    (AlgebraicStacks.isFlat_and_isLocallyOfFinitePresentation_of_isGerbeOver B S hS h hh).1
  have haflat : AlgebraicStacks.IsFlat B S hS a :=
    AlgebraicStacks.isFlat_of_isSmooth B S hS a hasm
  have hflat : AlgebraicStacks.IsFlat B S hS (a ≫ h) :=
    hasPropertyOnSomeSmoothDiagram_isFlat_comp B S hS a.hom h.hom haflat hhflat
  have hsurj : IsSurjective B S hS (a ≫ h) :=
    isSurjective_comp B S hS a h hasurj (isSurjective_of_isGerbeOver B S hS h hh)
  have hm := isFlat_representingMap_of_isFlat B S hS (yoneda.obj A) (yoneda.obj U)
    (isAlgebraicSpace_yoneda B S hS A) (isAlgebraicSpace_yoneda B S hS U)
    (representedChart B S hS A) (representedChart B S hS U) (a ≫ h) hflat
  have hms := isSurjective_representingMap_of_isSurjective B S hS (yoneda.obj A) (yoneda.obj U)
    (representedChart B S hS A) (representedChart B S hS U) (a ≫ h) hsurj
  have hAred : Space.HasEtaleLocalProperty B S hS (yoneda.obj A)
      (fun T : Scheme.{u} => IsReduced T) :=
    (Space.exists_atlas_iff_of_representable B S hS (yoneda.obj A)
      (fun T : Scheme.{u} => IsReduced T) A (Iso.refl _)).2 hA
  exact (Space.exists_atlas_iff_of_representable B S hS (yoneda.obj U)
    (fun T : Scheme.{u} => IsReduced T) U (Iso.refl _)).1
    (Space.isReduced_of_flat_of_surjective B S hS (isAlgebraicSpace_yoneda B S hS A)
      (isAlgebraicSpace_yoneda B S hS U) _ hm hms hAred)

/-- **An open substack of a reduced irreducible algebraic stack which is a gerbe over a nonempty
scheme has integral base.** The base `U` is reduced by
`AlgebraicGeometry.Stack.isReduced_of_isGerbeOver_schemeStack`, the open substack being reduced.
Its underlying space is the space of points of its algebraic stack (Stacks 04XL), onto which the
gerbe is a homeomorphism (**Stacks 06R9**); and the space of points of the open substack is
irreducible, being nonempty and openly embedded in the irreducible `|𝒳|` (**Stacks 0H20**). -/
theorem isIntegral_of_isGerbeOver_openSubstack {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (hred : IsReducedStack B S hS 𝒳)
    (hirr : @IrreducibleSpace (AlgebraicStacks.points B S hS 𝒳) (pointTopology B S hS 𝒳.val))
    (𝒰 : OpenSubstack 𝒳) {U : BigFppfOver B S hS}
    (h : 𝒰.toAlgebraicStack ⟶ schemeStack.{u, w} B S hS U)
    (hh : AlgebraicStacks.IsGerbeOver B S hS h)
    (hU : Nonempty ((BigFppfOver.toScheme B S hS).obj U)) :
    AlgebraicGeometry.IsIntegral ((BigFppfOver.toScheme B S hS).obj U) := by
  have := isReduced_of_isGerbeOver_schemeStack B S hS h hh (𝒰.isReducedStack B S hS hred)
  let := pointTopology B S hS 𝒳.val
  let := pointTopology B S hS 𝒰.toAlgebraicStack.val
  let := pointTopology B S hS (schemeStack.{u, w} B S hS U).val
  have hφ := isHomeomorph_pointsMap_of_isGerbeOver B S hS h hh
  let ψ := pointsHomeomorphScheme B S hS U
  have : Nonempty (AlgebraicStacks.points B S hS 𝒰.toAlgebraicStack) := by
    obtain ⟨t⟩ := hU
    obtain ⟨x, -⟩ := hφ.surjective (ψ.symm t)
    exact ⟨x⟩
  have hemb : Topology.IsOpenEmbedding (AlgebraicStacks.pointsMap B S hS 𝒰.inclusion) :=
    Topology.IsOpenEmbedding.of_isEmbedding_isOpenMap
      (AlgebraicStacks.isEmbedding_pointsMap_of_isImmersion B S hS _
        (𝒰.isImmersion_inclusion B S hS))
      (AlgebraicStacks.isOpenMap_pointsMap_of_isOpenImmersion B S hS _ 𝒰.isOpenImmersion)
  have := hemb.irreducibleSpace
  have : IrreducibleSpace (AlgebraicStacks.points B S hS (schemeStack.{u, w} B S hS U)) :=
    hφ.surjective.irreducibleSpace hφ.continuous
  have : IrreducibleSpace ((BigFppfOver.toScheme B S hS).obj U) :=
    ψ.surjective.irreducibleSpace ψ.continuous
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- **Stacks 0GWC, part (2).** Let `𝒳` be an integral algebraic stack over `S` (**Stacks 0GWB**).
Then there is an open substack `𝒰 ⊆ 𝒳` which is a gerbe over an integral scheme `U`: a 1-morphism
from `𝒰` to the algebraic stack of the scheme `U` making `𝒰` a gerbe over it (**Stacks 06QC**).

By **Stacks 06RC** a dense open substack `𝒲` is a gerbe over an algebraic space `Y`. `𝒲` is
decent (**Stacks 0GW3**), hence so is `Y` (**Stacks 0GW5**), and a decent algebraic space has a
dense open subspace which is a scheme `U` (Spaces over Fields, Section 0AD3). The base change of
`𝒲 ⟶ Y` to `U` is the open substack `𝒰`, a gerbe over `U`; and `U` is integral: reduced since
`𝒰` is, and irreducible since `|U| = |𝒰|` is a nonempty open of the irreducible `|𝒳|`. -/
theorem exists_openSubstack_isGerbeOver_isIntegral (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (h𝒳 : IsIntegral B S hS 𝒳) :
    ∃ (𝒰 : OpenSubstack 𝒳) (U : BigFppfOver B S hS),
      AlgebraicGeometry.IsIntegral ((BigFppfOver.toScheme B S hS).obj U) ∧
        ∃ f : 𝒰.toAlgebraicStack ⟶ schemeStack.{u, w} B S hS U,
          AlgebraicStacks.IsGerbeOver B S hS f := by
  obtain ⟨hred, hdec, hqc, hirr⟩ := h𝒳
  obtain ⟨W, hWd, 𝒴, ⟨F, hF, ⟨E⟩⟩, g, hg⟩ :=
    exists_openSubstack_dense_isGerbe B S hS 𝒳 hred hqc
  have hFdec : Space.IsDecentSpace B S hS F :=
    isDecentSpace_of_isDecent_representing B S hS 𝒴.val
      (isDecent_of_isGerbeOver B S hS g hg (W.isDecent B S hS hdec)) F hF E
  obtain ⟨G, hGopen, hGrep, hGdense⟩ :=
    Space.exists_denseRange_isRepresentable_isOpenSubspace_of_isDecentSpace B S hS hF hFdec
  let U := G.toFunctor.reprX
  let eU : yoneda.obj U ≅ G.toFunctor := G.toFunctor.reprW
  have hiU : Space.IsOpenImmersion B S hS (eU.hom ≫ G.ι) :=
    MorphismProperty.RespectsIso.precomp _ eU.hom G.ι hGopen.2
  obtain ⟨j, hj⟩ := exists_oneMorphism_representingMap_eq B S hS
    (𝒳 := schemeStack.{u, w} B S hS U) (𝒴 := 𝒴) (yoneda.obj U) F
    (representedChart B S hS U) E (eU.hom ≫ G.ι)
  have hjo : AlgebraicStacks.IsOpenImmersion B S hS j :=
    AlgebraicStacks.isOpenImmersion_of_isOpenImmersion_representingMap B S hS j (yoneda.obj U) F
      (isAlgebraicSpace_yoneda B S hS U) hF
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS U)
      (representedChart B S hS U) E (hj ▸ hiU)
  obtain ⟨𝒰, h, hh⟩ :=
    AlgebraicStacks.exists_openSubstack_isGerbeOver_of_isOpenImmersion B S hS W g hg j hjo
  refine ⟨𝒰, U, isIntegral_of_isGerbeOver_openSubstack B S hS hred hirr 𝒰 h hh ?_, h, hh⟩
  -- the scheme `U` is nonempty
  let := pointTopology B S hS 𝒳.val
  let := Space.pointTopology B S hS F
  let := pointTopology B S hS 𝒴.val
  have : Nonempty (AlgebraicStacks.points B S hS 𝒳) := hirr.toNonempty
  obtain ⟨_, ⟨x, rfl⟩⟩ := hWd.nonempty
  obtain ⟨y, -⟩ := (isHomeomorph_spacePointMap_representing B S hS F hF 𝒴.val E).surjective
    (AlgebraicStacks.pointsMap B S hS g x)
  have : Nonempty (Space.points B S hS F) := ⟨y⟩
  obtain ⟨z⟩ := hGdense.nonempty
  exact ⟨Space.pointsEquivScheme B S hS U (Space.pointsMap B S hS G.toFunctor eU.inv z)⟩

/-- **Stacks 0GWC, part (1).** The space of points `|𝒳|` of an integral algebraic stack `𝒳` over
`S` (**Stacks 0GWB**) is sober in the sense of Stacks 004X, irreducible, and has a unique generic
point.

Sobriety is **Stacks 0GW9**, `𝒳` being decent with quasi-compact inertia projection;
irreducibility is part of integrality; and the unique generic point of the irreducible closed set
`|𝒳|` is given by sobriety. -/
theorem stacksSober_irreducibleSpace_existsUnique_isGenericPoint_of_isIntegral
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (h𝒳 : IsIntegral B S hS 𝒳) :
    letI := pointTopology B S hS 𝒳.val
    StacksSober (AlgebraicStacks.points B S hS 𝒳) ∧
      IrreducibleSpace (AlgebraicStacks.points B S hS 𝒳) ∧
        ∃! x : AlgebraicStacks.points B S hS 𝒳, IsGenericPoint x Set.univ := by
  let := pointTopology B S hS 𝒳.val
  have hs := AlgebraicStacks.stacksSober_points_of_isDecent 𝒳 h𝒳.2.1 h𝒳.2.2.1
  have : IrreducibleSpace (AlgebraicStacks.points B S hS 𝒳) := h𝒳.2.2.2
  obtain ⟨x, ⟨-, hx⟩, huniq⟩ := hs Set.univ (IrreducibleSpace.isIrreducible_univ _) isClosed_univ
  exact ⟨hs, inferInstance, x, hx.symm, fun y hy => huniq y ⟨trivial, hy.symm⟩⟩

/-- **Stacks 0GWC.** Let `𝒳` be an integral algebraic stack over `S` (**Stacks 0GWB**). Then
1. `|𝒳|` is sober (Stacks 004X), irreducible, and has a unique generic point;
2. there is an open substack `𝒰 ⊆ 𝒳` which is a gerbe over an integral scheme `U`: a 1-morphism
   from `𝒰` to the algebraic stack of `U` making `𝒰` a gerbe over it (**Stacks 06QC**).

The two parts are
`AlgebraicGeometry.Stack.stacksSober_irreducibleSpace_existsUnique_isGenericPoint_of_isIntegral`
and `AlgebraicGeometry.Stack.exists_openSubstack_isGerbeOver_isIntegral`. -/
@[stacks 0GWC]
theorem stacksSober_and_exists_openSubstack_isGerbeOver_of_isIntegral
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (h𝒳 : IsIntegral B S hS 𝒳) :
    (letI := pointTopology B S hS 𝒳.val;
      StacksSober (AlgebraicStacks.points B S hS 𝒳) ∧
        IrreducibleSpace (AlgebraicStacks.points B S hS 𝒳) ∧
          ∃! x : AlgebraicStacks.points B S hS 𝒳, IsGenericPoint x Set.univ) ∧
      ∃ (𝒰 : OpenSubstack 𝒳) (U : BigFppfOver B S hS),
        AlgebraicGeometry.IsIntegral ((BigFppfOver.toScheme B S hS).obj U) ∧
          ∃ f : 𝒰.toAlgebraicStack ⟶ schemeStack.{u, w} B S hS U,
            AlgebraicStacks.IsGerbeOver B S hS f :=
  ⟨stacksSober_irreducibleSpace_existsUnique_isGenericPoint_of_isIntegral B S hS 𝒳 h𝒳,
    exists_openSubstack_isGerbeOver_isIntegral B S hS 𝒳 h𝒳⟩

end AlgebraicGeometry.Stack

end
