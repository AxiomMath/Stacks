module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.FaithfullyFlatSections
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineSurjectiveIndexChart
public import StacksFrontier.AlgebraicGeometry.Spaces.MorphismKernelIdeal

/-!
# A function killed by the structure map vanishes wherever the morphism has a lift

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B`, let `U` be an étale scheme chart of `Y`, and let `s` be a regular function on `U`
lying in the kernel `AlgebraicGeometry.Space.kernelIdealSheaf` of the structure map
`f♯ : 𝒪_Y ⟶ f_*𝒪_X` of Stacks 03G8.  A scheme `a` of the big fppf site equipped with a
morphism `k : a ⟶ U` and a lift `y : a ⟶ X` of `k` along `f` lies, so to speak, inside the
image of `f` above `U`, and `s` has to vanish on it.

The kernel is computed chart by chart: `AlgebraicGeometry.Space.mem_ker_structureSharp_iff`
says that `s` pulls back to zero on *every* étale scheme chart of `X` above `X ×_Y U`.  The
chart used here is the fibre product `T ×_Y U` of the chart `U` of `Y` with a scheme atlas `T`
of `X`.  It is a scheme because `U ⟶ Y` is representable, it is étale over `X` because it is
étale over `T` and `T` is étale over `X`, and it carries a projection to `U`; the chart
diagram of Stacks 03G3 so obtained converts it into an index object of the chartwise
computation.  The lift `y` is what makes `a` accessible: the scheme `P = a ×_X T` covers `a`
and maps to `T ×_Y U` compatibly with the two morphisms to `U`, so the pullback of `s` to `P`
factors through `T ×_Y U`, where `s` already vanishes.  Finally `P ⟶ a` is a base change of
the atlas, hence étale and surjective, so it is flat and surjective and
`AlgebraicGeometry.Scheme.Hom.appTop_injective_of_flat_of_surjective` carries the vanishing
on `P` back to `a`.

No hypothesis on `f` is needed: neither representability nor quasi-compactness.

## Main results

* `AlgebraicGeometry.Space.exists_isPullback_etale_surjective_atlas`: a scheme over an
  algebraic space is covered by an étale surjective morphism from its fibre product with a
  scheme atlas of that space.
* `AlgebraicGeometry.Space.exists_etaleChart_isPullback_of_presheafEtale`: the fibre product
  of an étale scheme chart of `Y` with a scheme étale over `X` is an étale scheme chart of
  `X`, cartesian over `Y`.
* `AlgebraicGeometry.Space.ker_comp_le_ker_of_injective`: pullback of regular functions along
  a morphism which is injective on global sections reflects vanishing.
* `AlgebraicGeometry.Space.kernelIdealSheaf_le_ker_of_chart`: a regular function killed by
  `f♯` vanishes on every étale scheme chart of `X` mapping to `U` over `f`.
* `AlgebraicGeometry.Space.kernelIdealSheaf_le_ker_of_lift`: a regular function on an étale
  scheme chart `U` of `Y` killed by `f♯` vanishes on every scheme over `U` which lifts to `X`
  along `f`.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03G3](https://stacks.math.columbia.edu/tag/03G3)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 025Y](https://stacks.math.columbia.edu/tag/025Y)
* [Stacks Project, Tag 02VW](https://stacks.math.columbia.edu/tag/02VW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Covering a scheme over an algebraic space -/

/-- A scheme `a` over an algebraic space `Z` is covered by the fibre product of `a` with a
scheme atlas of `Z`: the projection to `a` is a base change of the atlas, hence étale and
surjective. -/
theorem exists_isPullback_etale_surjective_atlas (Z : AlgebraicSpaces B S hS)
    {a : BigFppfOver B S hS} (y : yoneda.obj a ⟶ Z.1) :
    ∃ (T P : BigFppfOver B S hS) (t : yoneda.obj T ⟶ Z.1) (p : P ⟶ a) (r : P ⟶ T),
      (MorphismProperty.inverseImage
          (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf t ∧
        IsPullback (yoneda.map r) (yoneda.map p) t y ∧
        Etale ((BigFppfOver.toScheme B S hS).map p) ∧
        Surjective ((BigFppfOver.toScheme B S hS).map p) := by
  obtain ⟨T, t, htSurj, htEtale⟩ := Z.property.exists_atlas
  exact ⟨T, htEtale.rep.pullback y, t, htEtale.rep.snd y, htEtale.rep.fst' y, htEtale,
    htEtale.rep.isPullback' y,
    htEtale.property y (htEtale.rep.fst y) (htEtale.rep.snd y) (htEtale.rep.isPullback y),
    htSurj.property y (htEtale.rep.fst y) (htEtale.rep.snd y) (htEtale.rep.isPullback y)⟩

/-! ### Reflecting vanishing along a morphism injective on sections -/

/-- Pullback of regular functions along a composite kills no more than pullback along its
second factor as soon as pullback along the first factor is injective. This is the converse
inclusion to `AlgebraicGeometry.Space.ker_le_ker_comp`, under that hypothesis. -/
theorem ker_comp_le_ker_of_injective {T₁ T₂ T₃ : BigFppfOver B S hS} (m : T₁ ⟶ T₂)
    (n : T₂ ⟶ T₃)
    (hm : Function.Injective (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map m).op).hom) :
    RingHom.ker (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (m ≫ n)).op).hom ≤
      RingHom.ker (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map n).op).hom := by
  intro b hb
  rw [RingHom.mem_ker, Functor.map_comp, op_comp, Functor.map_comp, CommRingCat.hom_comp,
    RingHom.coe_comp, Function.comp_apply] at hb
  exact RingHom.mem_ker.2 (hm (hb.trans (map_zero _).symm))

variable {X Y : AlgebraicSpaces B S hS}

/-! ### The fibre product of a chart of the target with a scheme étale over the source -/

/-- The fibre product of an étale scheme chart `U` of `Y` with a scheme `T` étale over `X` is
again a scheme, and it is an étale scheme chart of `X`: it is representable because `U ⟶ Y`
is, it is étale over `T` because `U ⟶ Y` is étale, and `T` is étale over `X`. -/
theorem exists_etaleChart_isPullback_of_presheafEtale (f : X ⟶ Y)
    (U : SmallEtale B S hS Y.1) {T : BigFppfOver B S hS} (t : yoneda.obj T ⟶ X.1)
    (ht : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf t) :
    ∃ (W : SmallEtale B S hS X.1)
      (c : (SmallEtale.toOver B S hS X.1).obj W ⟶ T)
      (g : (SmallEtale.toOver B S hS X.1).obj W ⟶ (SmallEtale.toOver B S hS Y.1).obj U),
      W.1.hom ≫ f.hom = yoneda.map g ≫ U.1.hom ∧
        IsPullback (yoneda.map g) (yoneda.map c) U.1.hom (t ≫ f.hom) := by
  have hpb : IsPullback (yoneda.map (U.2.rep.fst' (t ≫ f.hom)))
      (yoneda.map (U.2.rep.snd (t ≫ f.hom))) U.1.hom (t ≫ f.hom) :=
    U.2.rep.isPullback' (t ≫ f.hom)
  have hcEtale : Etale ((BigFppfOver.toScheme B S hS).map (U.2.rep.snd (t ≫ f.hom))) :=
    U.2.property (t ≫ f.hom) (U.2.rep.fst (t ≫ f.hom)) (U.2.rep.snd (t ≫ f.hom))
      (U.2.rep.isPullback (t ≫ f.hom))
  refine ⟨⟨CostructuredArrow.mk (yoneda.map (U.2.rep.snd (t ≫ f.hom)) ≫ t),
      etale_comp_of_scheme B S hS (U.2.rep.snd (t ≫ f.hom)) t hcEtale ht⟩,
    U.2.rep.snd (t ≫ f.hom), U.2.rep.fst' (t ≫ f.hom), ?_, hpb⟩
  change (yoneda.map (U.2.rep.snd (t ≫ f.hom)) ≫ t) ≫ f.hom =
    yoneda.map (U.2.rep.fst' (t ≫ f.hom)) ≫ U.1.hom
  rw [Category.assoc]
  exact hpb.w.symm

/-! ### Vanishing of a kernel section -/

/-- A regular function on an étale scheme chart `U` of `Y` killed by the structure map
`f♯ : 𝒪_Y ⟶ f_*𝒪_X` vanishes on every étale scheme chart of `X` mapping to `U` over `f`: such
a chart with such a morphism is a chart diagram of Stacks 03G3, hence names an étale scheme
chart of `X` above `X ×_Y U`, and those are exactly the charts over which the kernel of the
structure map is computed. -/
theorem kernelIdealSheaf_le_ker_of_chart (f : X ⟶ Y) (U : SmallEtale B S hS Y.1)
    (W : SmallEtale B S hS X.1)
    (g : (SmallEtale.toOver B S hS X.1).obj W ⟶ (SmallEtale.toOver B S hS Y.1).obj U)
    (hg : W.1.hom ≫ f.hom = yoneda.map g ≫ U.1.hom) :
    (kernelIdealSheaf B S hS f).obj (op U) ≤
      RingHom.ker (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map g).op).hom := by
  have e : chartBaseChangeMap B S hS f U (indexOfChartDiagram B S hS f ⟨W, U, g, hg⟩) = g :=
    chartBaseChangeMap_indexOfChartDiagram B S hS f ⟨W, U, g, hg⟩
  intro s hs
  rw [← e]
  exact (mem_ker_structureSharp_iff B S hS f U s).1 hs
    (indexOfChartDiagram B S hS f ⟨W, U, g, hg⟩)

/-- **A regular function killed by the structure map vanishes where the morphism has a lift.**
Let `f : X ⟶ Y` be a morphism of algebraic spaces, let `U` be an étale scheme chart of `Y`,
and let `k : a ⟶ U` be a morphism of the big fppf site which lifts along `f` to a morphism
`y : a ⟶ X`. Then every regular function on `U` in the kernel of `f♯ : 𝒪_Y ⟶ f_*𝒪_X` pulls
back to zero on `a`.

Both the fibre product `a ×_X T` with a scheme atlas `T` of `X` and the étale chart `T ×_Y U`
of `X` are schemes; the first covers `a` flatly and surjectively and maps to the second, where
the function already vanishes because that chart is one of those computing the kernel of the
structure map. -/
theorem kernelIdealSheaf_le_ker_of_lift (f : X ⟶ Y) (U : SmallEtale B S hS Y.1)
    {a : BigFppfOver B S hS} (k : a ⟶ U.1.left) (y : yoneda.obj a ⟶ X.1)
    (hy : yoneda.map k ≫ U.1.hom = y ≫ f.hom) :
    (kernelIdealSheaf B S hS f).obj (op U) ≤
      RingHom.ker (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map k).op).hom := by
  obtain ⟨T, P, t, p, r, htEtale, hpbP, hpEtale, hpSurj⟩ :=
    exists_isPullback_etale_surjective_atlas B S hS X y
  obtain ⟨W, c, g, hcomm, hsqW⟩ :=
    exists_etaleChart_isPullback_of_presheafEtale B S hS f U t htEtale
  have hcone : yoneda.map (p ≫ k) ≫ U.1.hom = yoneda.map r ≫ t ≫ f.hom :=
    calc yoneda.map (p ≫ k) ≫ U.1.hom
        = yoneda.map p ≫ yoneda.map k ≫ U.1.hom := by
          rw [Functor.map_comp, Category.assoc]
      _ = (yoneda.map p ≫ y) ≫ f.hom := by rw [hy, Category.assoc]
      _ = (yoneda.map r ≫ t) ≫ f.hom := by rw [hpbP.w]
      _ = yoneda.map r ≫ t ≫ f.hom := Category.assoc _ _ _
  obtain ⟨w, hw⟩ : ∃ w : P ⟶ (SmallEtale.toOver B S hS X.1).obj W, w ≫ g = p ≫ k :=
    ⟨yoneda.preimage (hsqW.lift (yoneda.map (p ≫ k)) (yoneda.map r) hcone),
      yoneda.map_injective (by
        rw [Functor.map_comp, Functor.map_preimage]
        exact hsqW.lift_fst _ _ _)⟩
  have hinj : Function.Injective
      (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map p).op).hom := by
    rw [Scheme.Γ_map_op]
    exact Scheme.Hom.appTop_injective_of_flat_of_surjective _
  refine le_trans (kernelIdealSheaf_le_ker_of_chart B S hS f U W g hcomm) ?_
  refine le_trans (ker_le_ker_comp B S hS w g) ?_
  rw [hw]
  exact ker_comp_le_ker_of_injective B S hS p k hinj

end AlgebraicGeometry.Space

end
