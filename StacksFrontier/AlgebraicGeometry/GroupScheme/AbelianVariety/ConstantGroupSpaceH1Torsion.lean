module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianSchemeFirstCohomologyInjective
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.GroupAlgebraicSpacePointsSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartRespectsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothGroupFirstCohomologyTorsion
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothSourceLocalityTransfer
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.OverMapRestrictTorsor

/-!
# First cohomology of a constant abelian variety over a two dimensional regular base is torsion

Let `A` be an abelian variety over a field `k`, let `G` be the commutative group algebraic space
over `Spec k` attached to it (Stacks 043I), and let `U` be an object of the big fppf site of
`Spec k` whose scheme `W` is a two dimensional regular integral Noetherian scheme. Then every
class in `H¹(U, G) = H¹((Sch/U)_fppf, G|_U)` has finite order. This is the combination of
Stacks 0AF9 (restriction to the generic point `Spec K` of `W` is injective on first cohomology
of the abelian scheme `A_W`) and Stacks 0AFA (first cohomology of a smooth commutative group
algebraic space over the field `K` is torsion), as used in the discussion before Stacks 0CXX.

## Main definitions

* `AlgebraicGeometry.Space.GroupAlgebraicSpace.genericPointOver`: the generic point `Spec K` of
  the scheme of `U`, as an object of the big fppf site of `Spec k`.
* `AlgebraicGeometry.Space.GroupAlgebraicSpace.h1RestrictGenericPoint`: restriction
  `H¹(U, G) → H¹((Sch/Spec K)_fppf, G|_{Spec K})`.

## Main results

* `AlgebraicGeometry.isSmooth_pointsSheaf`: the abelian sheaf of points of a smooth commutative
  group scheme over `W`, read as an algebraic space, is smooth over `W`.
* `AlgebraicGeometry.Space.GroupAlgebraicSpace.isOfFinAddOrder_h1RestrictGenericPoint`: the
  restriction of a class to `Spec K` has finite order (Stacks 0AFA).
* `torsorIsoClassesEquivH1_eq_zero_of_h1RestrictGenericPoint` (same namespace): a torsor
  whose class restricts to zero at `Spec K` has zero class (Stacks 0AF9).
* `AlgebraicGeometry.Space.GroupAlgebraicSpace.isOfFinAddOrder_h1_over_of_dim_two`: **every
  class in `H¹(U, G)` has finite order**.

## Implementation notes

The argument is run on torsors, not on cohomology of the site of `W`: the class of a torsor on
`(Sch/Spec k)_fppf / U` is restricted to `Spec K` with `Stacks.Cohomology.Torsors.overMapH1Restrict`
and the comparison along the equivalence of sites of Stacks 06WI, where Stacks 0AFA applies, and
a section over `Spec K` is carried to the big fppf site of `W`, where Stacks 0AF9 applies to the
torsor read under the abelian scheme `A_W`. No comparison between the cohomology of a localized
site and Mathlib's `CategoryTheory.Sheaf.H'` is needed.

## References

* [Stacks Project, Tag 0AF9](https://stacks.math.columbia.edu/tag/0AF9)
* [Stacks Project, Tag 0AFA](https://stacks.math.columbia.edu/tag/0AFA)
* [Stacks Project, Tag 0CXX](https://stacks.math.columbia.edu/tag/0CXX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (W : Scheme.{u}) (hW : B.Contains W)

/-- **The points of a smooth commutative group scheme over `W` form an algebraic space smooth
over `W`**: by Stacks 03MJ for representable presheaves
(`AlgebraicGeometry.Space.isSmooth_yoneda_map_iff`), the structure morphism of the represented
presheaf is smooth exactly when that of the group scheme is. -/
theorem isSmooth_pointsSheaf (G : Over W) [GrpObj G] [IsCommMonObj G] [Smooth G.hom]
    (hG : B.Contains G.left) :
    Space.IsSmooth B W hW
      (terminal.from ((pointsSheaf B W hW G hG).obj ⋙ forget AddCommGrpCat)) := by
  refine (Space.holdsOnEveryEtaleChart_terminal_iff_of_iso B W hW (@Smooth.{u})
    (pointsSheafYonedaIso B W hW G hG).symm).2 ?_
  have hT := Space.isTerminal_yoneda_obj_base B W hW
  rw [show terminal.from (yoneda.obj (groupSchemeObj B W hW G hG)) =
      yoneda.map (Over.mkIdTerminal.from (groupSchemeObj B W hW G hG)) ≫
        (hT.conePointUniqueUpToIso terminalIsTerminal).hom from terminal.hom_ext _ _]
  let Q : MorphismProperty ((BigFppfOver B W hW)ᵒᵖ ⥤ Type u) :=
    fun _ _ f => Space.HoldsOnEveryEtaleChart B W hW (@Smooth.{u}) f
  let : Q.RespectsIso := Space.holdsOnEveryEtaleChart_respectsIso_presheaf B W hW _
  refine (Q.cancel_right_of_respectsIso _ _).2 ?_
  have hl : (Over.mkIdTerminal.from (groupSchemeObj B W hW G hG)).left =
      (groupSchemeObj B W hW G hG).hom := by
    simp
  have hmap : (BigFppfOver.toScheme B W hW).map
      (Over.mkIdTerminal.from (groupSchemeObj B W hW G hG)) = G.hom :=
    congrArg (fun g => B.inclusion.map g) hl
  exact (Space.isSmooth_yoneda_map_iff B W hW _).2 (by rw [hmap]; exact ‹Smooth G.hom›)

end AlgebraicGeometry

namespace AlgebraicGeometry.Space.GroupAlgebraicSpace

open Stacks.Cohomology.Torsors

variable {𝒞 : BigFppfSite.{u}} {k : Type u} [Field k] {hk : 𝒞.Contains (Spec (.of k))}
  (U : BigFppfOver 𝒞 (Spec (.of k)) hk)

/-- The generic point of the scheme `W` of an object `U` of the big fppf site of `Spec k`, as an
object of that site: `Spec K → W → Spec k` for the function field `K` of `W`. -/
abbrev genericPointOver [IrreducibleSpace (BigFppfOver.objScheme 𝒞 _ hk U)]
    (hK : 𝒞.Contains (Spec (BigFppfOver.objScheme 𝒞 _ hk U).functionField)) :
    BigFppfOver 𝒞 (Spec (.of k)) hk :=
  ((BigFppfOver.objEquiv 𝒞 _ hk U).functor.obj (genericPointObj 𝒞 _
    (BigFppfOver.contains_objScheme 𝒞 _ hk U) hK)).left

/-- The morphism `Spec K → U` of the big fppf site of `Spec k` from the generic point of the
scheme of `U`. -/
abbrev genericPointOverHom [IrreducibleSpace (BigFppfOver.objScheme 𝒞 _ hk U)]
    (hK : 𝒞.Contains (Spec (BigFppfOver.objScheme 𝒞 _ hk U).functionField)) :
    genericPointOver U hK ⟶ U :=
  ((BigFppfOver.objEquiv 𝒞 _ hk U).functor.obj (genericPointObj 𝒞 _
    (BigFppfOver.contains_objScheme 𝒞 _ hk U) hK)).hom

attribute [local instance] Stacks.Cohomology.LocalizedSite.preservesFiniteColimits_overMapPullback

variable (A : Over (Spec (.of k))) [GrpObj A] (hA : 𝒞.Contains A.left)
  [IsIntegral (BigFppfOver.objScheme 𝒞 _ hk U)]
  (hK : 𝒞.Contains (Spec (BigFppfOver.objScheme 𝒞 _ hk U).functionField))
  [∀ V : BigFppfOver 𝒞 (Spec (.of k)) hk,
    HasSheafify ((BigFppfOver.topology 𝒞 _ hk).over V) AddCommGrpCat.{u}]
  [∀ V : BigFppfOver 𝒞 (Spec (.of k)) hk,
    HasExt.{w} (Sheaf ((BigFppfOver.topology 𝒞 _ hk).over V) AddCommGrpCat.{u})]
  [∀ V : BigFppfOver 𝒞 (Spec (.of k)) hk,
    ((BigFppfOver.topology 𝒞 _ hk).over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (BigFppfOver.topology 𝒞 (BigFppfOver.objScheme 𝒞 _ hk (genericPointOver U hK))
    (BigFppfOver.contains_objScheme 𝒞 _ hk (genericPointOver U hK))) AddCommGrpCat.{u}]
  [HasExt.{w} (Sheaf (BigFppfOver.topology 𝒞
    (BigFppfOver.objScheme 𝒞 _ hk (genericPointOver U hK))
    (BigFppfOver.contains_objScheme 𝒞 _ hk (genericPointOver U hK))) AddCommGrpCat.{u})]
  [EnoughInjectives (Sheaf (BigFppfOver.topology 𝒞
    (BigFppfOver.objScheme 𝒞 _ hk (genericPointOver U hK))
    (BigFppfOver.contains_objScheme 𝒞 _ hk (genericPointOver U hK))) AddCommGrpCat.{u})]

/-- **Restriction of `H¹(U, G)` to the generic point of the scheme of `U`**, read on the big fppf
site of `Spec K`: the restriction `Stacks.Cohomology.Torsors.overMapH1Restrict` along
`Spec K → U`, followed by the comparison of cohomology along the equivalence of sites of
Stacks 06WI (`Stacks.Cohomology.DenseSubsite.hAddEquiv`). -/
def h1RestrictGenericPoint [IsCommMonObj A] :
    Sheaf.H.{w} ((pointsSheaf (ofGroupScheme (hS := hk) A hA)).over U) 1 →+
      Sheaf.H.{w} (pointsSheafOnObjScheme (ofGroupScheme (hS := hk) A hA)
        (genericPointOver U hK)) 1 :=
  (Stacks.Cohomology.DenseSubsite.hAddEquiv
    (BigFppfOver.topology 𝒞 _ (BigFppfOver.contains_objScheme 𝒞 _ hk (genericPointOver U hK)))
    ((BigFppfOver.topology 𝒞 _ hk).over (genericPointOver U hK))
    (BigFppfOver.objEquiv 𝒞 _ hk (genericPointOver U hK)).functor
    (((BigFppfOver.topology 𝒞 _ hk).overMapPullback AddCommGrpCat.{u}
      (genericPointOverHom U hK)).obj ((pointsSheaf (ofGroupScheme (hS := hk) A hA)).over U))
    1).toAddMonoidHom.comp
    (overMapH1Restrict (BigFppfOver.topology 𝒞 _ hk) (genericPointOverHom U hK) _ 1)

omit [IsIntegral (BigFppfOver.objScheme 𝒞 _ hk U)]
  [∀ V : BigFppfOver 𝒞 (Spec (.of k)) hk,
    ((BigFppfOver.topology 𝒞 _ hk).over V).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- A torsor on the site localized at `U` with a section over the image of the terminal object
of the big fppf site of the scheme of `U` has zero class: that image is terminal. -/
theorem torsorIsoClassesEquivH1_eq_zero_of_section_objEquiv
    {H : Sheaf ((BigFppfOver.topology 𝒞 _ hk).over U) AddCommGrpCat.{u}} (Q : AbelianTorsor H)
    (x : Q.1.presheaf.obj (op ((BigFppfOver.objEquiv 𝒞 _ hk U).functor.obj (Over.mk (𝟙 _))))) :
    torsorIsoClassesEquivH1 H (Quotient.mk (torsorSetoid H) Q) = 0 := by
  rw [torsorIsoClassesEquivH1_eq_zero_iff, nonempty_globalSections_iff_sectionFamily]
  let hT := Over.mkIdTerminal.isTerminalObj (BigFppfOver.objEquiv 𝒞 _ hk U).functor _
  refine ⟨fun V => Q.1.presheaf.map (hT.from V.unop).op x, ?_⟩
  intro V V' g
  change Q.1.presheaf.map g (Q.1.presheaf.map (hT.from V.unop).op x) =
    Q.1.presheaf.map (hT.from V'.unop).op x
  rw [← Functor.map_comp_apply]
  exact congrArg (fun h => Q.1.presheaf.map h x) (Quiver.Hom.unop_inj (hT.hom_ext _ _))

variable [IsAbelianVariety k A]

/-- **Stacks 0AFA at the generic point**: the restriction to the generic point `Spec K` of a
class in `H¹(U, G)` has finite order, since it lies in the first cohomology of the smooth
commutative group algebraic space `A_K` over the field `K`
(`AlgebraicGeometry.Space.fppfH1_isAddTorsion`). -/
theorem isOfFinAddOrder_h1RestrictGenericPoint
    (hAK : 𝒞.Contains
      (groupSchemeBaseChange A (BigFppfOver.objHom 𝒞 _ hk (genericPointOver U hK))).left)
    (c : Sheaf.H.{w} ((pointsSheaf (ofGroupScheme (hS := hk) A hA)).over U) 1) :
    letI : IsCommMonObj A := isCommMonObj_of_isProper_of_geometricallyIntegral A
    IsOfFinAddOrder (h1RestrictGenericPoint U A hA hK c) := by
  let : IsCommMonObj A := isCommMonObj_of_isProper_of_geometricallyIntegral A
  let X := genericPointOver U hK
  let e := pointsSheafOnObjSchemeIso A hA X hAK
  have halg : IsAlgebraicSpace 𝒞 _ (BigFppfOver.contains_objScheme 𝒞 _ hk X)
      ((pointsSheafOnObjScheme (ofGroupScheme (hS := hk) A hA) X).obj ⋙
        forget AddCommGrpCat) :=
    isAlgebraicSpace_of_iso _ _ _
      (Functor.isoWhiskerRight ((sheafToPresheaf _ _).mapIso e) (forget AddCommGrpCat)).symm
      (isAlgebraicSpace_pointsSheaf _ _ _ _ hAK)
  let AX := groupSchemeBaseChange A (BigFppfOver.objHom 𝒞 _ hk X)
  have hAXs : Smooth AX.hom := smooth_of_isAbelianScheme AX
  have hsm : IsSmooth 𝒞 _ (BigFppfOver.contains_objScheme 𝒞 _ hk X)
      (terminal.from ((pointsSheafOnObjScheme (ofGroupScheme (hS := hk) A hA) X).obj ⋙
        forget AddCommGrpCat)) :=
    (holdsOnEveryEtaleChart_terminal_iff_of_iso _ _ _ (@Smooth.{u})
      (Functor.isoWhiskerRight ((sheafToPresheaf _ _).mapIso e) (forget AddCommGrpCat))).2
      (@isSmooth_pointsSheaf 𝒞 _ (BigFppfOver.contains_objScheme 𝒞 _ hk X) AX _ _ hAXs hAK)
  have htors := @Space.fppfH1_isAddTorsion.{u, w}
    (BigFppfOver.objScheme 𝒞 _ hk U).functionField _ 𝒞
    (BigFppfOver.contains_objScheme 𝒞 _ hk X) ‹_› ‹_› _ halg hsm
  have htors' : IsAddTorsion (Sheaf.H.{w}
      (pointsSheafOnObjScheme (ofGroupScheme (hS := hk) A hA) X) 1) := htors
  exact htors' _

/-- **Stacks 0AF9 for `H¹(U, G)`**: a torsor under `G|_U` whose class restricts to zero at the
generic point `Spec K` of the scheme `W` of `U` has zero class, when `W` is a two dimensional
regular integral Noetherian scheme. Its restriction to `Spec K` has a section, so, read under
the abelian scheme `A_W` (`AlgebraicGeometry.Space.GroupAlgebraicSpace.pointsSheafOnObjSchemeIso`),
it has a section over the generic point and is trivial by
`AlgebraicGeometry.isTrivial_of_nonempty_sections_genericPoint`. -/
theorem torsorIsoClassesEquivH1_eq_zero_of_h1RestrictGenericPoint
    [AlgebraicGeometry.IsNoetherian (BigFppfOver.objScheme 𝒞 _ hk U)]
    (hreg : IsRegular (BigFppfOver.objScheme 𝒞 _ hk U))
    (hdim : topologicalKrullDim (BigFppfOver.objScheme 𝒞 _ hk U) = (2 : WithBot ℕ∞))
    (hAW : 𝒞.Contains (groupSchemeBaseChange A (BigFppfOver.objHom 𝒞 _ hk U)).left)
    (Q : AbelianTorsor ((pointsSheaf (ofGroupScheme (hS := hk) A hA)).over U))
    (hQ : letI : IsCommMonObj A := isCommMonObj_of_isProper_of_geometricallyIntegral A
      h1RestrictGenericPoint U A hA hK
        (torsorIsoClassesEquivH1 _ (Quotient.mk (torsorSetoid _) Q)) = 0) :
    torsorIsoClassesEquivH1 _ (Quotient.mk (torsorSetoid _) Q) = 0 := by
  let : IsCommMonObj A := isCommMonObj_of_isProper_of_geometricallyIntegral A
  let J := BigFppfOver.topology 𝒞 (Spec (.of k)) hk
  let W := BigFppfOver.objScheme 𝒞 _ hk U
  let hW := BigFppfOver.contains_objScheme 𝒞 _ hk U
  let η := (BigFppfOver.objEquiv 𝒞 _ hk U).functor.obj (genericPointObj 𝒞 W hW hK)
  let X := genericPointOver U hK
  let f : X ⟶ U := genericPointOverHom U hK
  have h0 := hQ
  change Stacks.Cohomology.DenseSubsite.hAddEquiv _ _ _ _ 1
    (overMapH1Restrict J f _ 1 _) = 0 at h0
  rw [← torsorIsoClassesEquivH1_overMapRestrict,
    Stacks.Cohomology.DenseSubsite.hAddEquiv_torsorIsoClassesEquivH1,
    torsorIsoClassesEquivH1_eq_zero_iff, nonempty_globalSections_iff_sectionFamily] at h0
  obtain ⟨s, -⟩ := h0
  let V0 : BigFppfOver 𝒞 (BigFppfOver.objScheme 𝒞 _ hk X)
      (BigFppfOver.contains_objScheme 𝒞 _ hk X) := Over.mk (𝟙 _)
  let m : η ⟶ (Over.map f).obj ((BigFppfOver.objEquiv 𝒞 _ hk X).functor.obj V0) :=
    Over.homMk (Over.homMk (𝟙 X.left) ((Category.id_comp _).trans (Category.id_comp _)))
      (by ext; exact (Category.id_comp _).trans (Category.id_comp _))
  let Q' := (Q.restrict (BigFppfOver.topology 𝒞 W hW) (J.over U)
    (BigFppfOver.objEquiv 𝒞 _ hk U).functor).transportIso (pointsSheafOnObjSchemeIso A hA U hAW)
  have htriv := isTrivial_of_nonempty_sections_genericPoint 𝒞 W hW hreg hdim hK _ hAW Q'
    ⟨Q.1.presheaf.map m.op (s (op V0))⟩
  obtain ⟨t', -⟩ := (nonempty_globalSections_iff_sectionFamily Q'.1.presheaf).1
    (nonempty_globalSections_of_isTrivial Q'.1 htriv)
  exact torsorIsoClassesEquivH1_eq_zero_of_section_objEquiv U Q (t' (op (Over.mk (𝟙 _))))

/-- **Every class in `H¹(U, G)` has finite order** when the scheme `W` of `U` is a two
dimensional regular integral Noetherian scheme, for the commutative group algebraic space `G` of
an abelian variety `A` over `k`. The restriction of a class `c` to the generic point `Spec K` of
`W` has finite order `n` by Stacks 0AFA
(`isOfFinAddOrder_h1RestrictGenericPoint`), and `n • c` is then zero by Stacks 0AF9
(`torsorIsoClassesEquivH1_eq_zero_of_h1RestrictGenericPoint`), both in the namespace
`AlgebraicGeometry.Space.GroupAlgebraicSpace`. -/
theorem isOfFinAddOrder_h1_over_of_dim_two
    [AlgebraicGeometry.IsNoetherian (BigFppfOver.objScheme 𝒞 _ hk U)]
    (hreg : IsRegular (BigFppfOver.objScheme 𝒞 _ hk U))
    (hdim : topologicalKrullDim (BigFppfOver.objScheme 𝒞 _ hk U) = (2 : WithBot ℕ∞))
    (hAW : 𝒞.Contains (groupSchemeBaseChange A (BigFppfOver.objHom 𝒞 _ hk U)).left)
    (hAK : 𝒞.Contains
      (groupSchemeBaseChange A (BigFppfOver.objHom 𝒞 _ hk (genericPointOver U hK))).left)
    (c : Sheaf.H.{w} ((pointsSheaf (ofGroupScheme (hS := hk) A hA)).over U) 1) :
    IsOfFinAddOrder c := by
  let : IsCommMonObj A := isCommMonObj_of_isProper_of_geometricallyIntegral A
  obtain ⟨n, hn, hnc⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.1
    (isOfFinAddOrder_h1RestrictGenericPoint U A hA hK hAK c)
  refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨n, hn, ?_⟩
  obtain ⟨q, hq⟩ := (torsorIsoClassesEquivH1 _).surjective (n • c)
  induction q using Quotient.inductionOn with | h Q => ?_
  rw [← hq]
  refine torsorIsoClassesEquivH1_eq_zero_of_h1RestrictGenericPoint U A hA hK hreg hdim hAW Q ?_
  rw [hq, map_nsmul]
  exact hnc

end AlgebraicGeometry.Space.GroupAlgebraicSpace

end
