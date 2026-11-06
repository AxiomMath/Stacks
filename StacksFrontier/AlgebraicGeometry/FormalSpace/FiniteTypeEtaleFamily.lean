module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.BoundedAtlas
public import StacksFrontier.AlgebraicGeometry.FormalSpace.DiagonalRepresentable
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteTypeRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableLocalOnSourceAndTargetRefined
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.RelativeLocalCriteria
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SchemeAtlasRefined

/-!
# A chart of a sheaf from a jointly surjective étale family, and local finite type

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` be a morphism of fppf
sheaves on the big fppf site of `S`, with `X` satisfying the set-theoretic condition of
**Stacks 0AIS** and `Y` a formal algebraic space over `S`. This file produces, at each
scheme-valued point `ξ : T ⟶ Y`, a single chart of the base change `T ×_Y X` out of a *family*
of representable étale morphisms into `X` which is jointly surjective as a family of morphisms
of sheaves, and uses it to descend the condition of Stacks 0AM4 — representability by algebraic
spaces together with the Bootstrap local finite type condition on every represented base change
— along such a family.

`AlgebraicGeometry.FormalSpace.IsLocallyOfFiniteType.of_comp_of_locallySurjective` does the
latter for a single surjective representable étale morphism, by producing one chart of the base
change at each `ξ` and feeding it to Stacks 0BGR and Stacks 03MJ. A family cannot be replaced by
the single morphism out of its coproduct: a coproduct of algebraic spaces over an index type of
`Type (u + 1)` need not be an algebraic space over `S`, because the disjoint union of their
scheme atlases is an object of the site only under a uniform size bound, and the cutoff of a big
fppf site carries no regularity. What is done instead is what the proof of the representability
assertion of **Stacks 0AIP** does for the relative product of two scheme-valued points: the
family of charts is cut down to one member per *point* of an object of the site surjecting onto
`T ×_Y X`, and each surviving member is shrunk to an affine open, whose size is bounded by that
of the surjecting object because an *affine* chart of a sheaf is no larger than one object of
the site covering it (`AlgebraicGeometry.FormalSpace.affineChart_size_le'`, the size estimate of
Stacks 0AIS, observation (2)). That family is indexed and sized below the cutoff, so
`AlgebraicGeometry.FormalSpace.exists_chart_of_size_le` glues it into a single chart.

The chart production asks nothing of the morphisms beyond representable étaleness, and
`AlgebraicGeometry.FormalSpace.exists_chart_of_etaleChartFamily` is therefore stated for a bare
family; what a *property* of the morphism being descended contributes is carried separately, as
the clause of that statement saying that every property of morphisms of schemes which is
Zariski-local at the source passes from the members of the family to the glued chart. Local
finite type uses that clause here, and representability by algebraic spaces — Stacks 0AN4,
conditions (4) and (5), in
`StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableEtaleFamily` — uses none of it.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_representable_locallySurjective_pullback`: the base
  change receives a locally surjective morphism from an object of the site, namely the fibre
  product of the point `ξ` with the surjection onto `X` given by Stacks 0AIS.
* `AlgebraicGeometry.FormalSpace.exists_chart_of_etaleChartFamily`: **a jointly surjective
  family of étale charts of a sheaf covered by one object of the site can be replaced by a
  single chart**, which inherits from the family every property Zariski-local at the source.
* `AlgebraicGeometry.FormalSpace.exists_schemeChart_pullback_of_etaleFamily`: the single chart
  of the base change which the family produces, locally of finite type over `T`.
* `AlgebraicGeometry.FormalSpace.IsLocallyOfFiniteType.of_etaleFamily`: **being locally of
  finite type is local on the source along a jointly surjective family of representable étale
  morphisms.**

## Implementation notes

The chart contributed by one member of the family is
`AlgebraicGeometry.FormalSpace.exists_memberChart_pullback`, which is stated for a single
representable étale morphism in
`StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableLocalOnSourceAndTarget` and knows
nothing of finite type; the local finite type of such a chart over `T` is read off the
every-étale-chart condition carried by `pᵢ ≫ f` inside
`AlgebraicGeometry.FormalSpace.exists_schemeChart_pullback_of_etaleFamily`.

That the image sieves of the member charts jointly cover at every section of `T ×_Y X` is
reduced in two steps to the joint surjectivity of the given family over `X`: base changing a
family does not disturb the covering property of its image sieves, limits of presheaves of types
being computed pointwise, and composing a family with locally surjective morphisms does not
either, by the local character of the topology. Those two steps are
`AlgebraicGeometry.FormalSpace.imageSieve_iSup_mem_pullback_fst` and
`AlgebraicGeometry.FormalSpace.imageSieve_iSup_mem_comp`, and they are stated for an arbitrary
site.

Local surjectivity of the glued chart is read off
`CategoryTheory.Presheaf.isLocallySurjective_sigmaDesc_of_fac`, whose commuting squares are the
fibre products inside the site of the chosen affine opens with the base changes of the members
along the surjection; the squares are *not* required to be cartesian, which is what lets the
affine opens be used in place of the members they sit inside.

## References

* [Stacks Project, Tag 02WQ](https://stacks.math.columbia.edu/tag/02WQ)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 04T7](https://stacks.math.columbia.edu/tag/04T7)
* [Stacks Project, Tag 0AHV](https://stacks.math.columbia.edu/tag/0AHV)
* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0AIP](https://stacks.math.columbia.edu/tag/0AIP)
* [Stacks Project, Tag 0AIS](https://stacks.math.columbia.edu/tag/0AIS)
* [Stacks Project, Tag 0AM4](https://stacks.math.columbia.edu/tag/0AM4)
* [Stacks Project, Tag 0AN4](https://stacks.math.columbia.edu/tag/0AN4)
* [Stacks Project, Tag 0BGR](https://stacks.math.columbia.edu/tag/0BGR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u w

/-! ### Joint surjectivity of a family, read off its image sieves -/

section Sieves

variable {C : Type*} [Category* C] (J : GrothendieckTopology C)

/-- **The image sieves of a base changed family still cover.** If the image sieves of a family
`{φᵢ : Aᵢ ⟶ F}` of morphisms of presheaves jointly cover at every section of `F`, then so do
the image sieves of the base changed family `{G ×_F Aᵢ ⟶ G}` at every section of `G`: a section
of `G` and a local lift of its image in `F` assemble to a local lift into the fibre product,
limits of presheaves of types being computed pointwise. -/
theorem imageSieve_iSup_mem_pullback_fst {ι : Type*} {A : ι → Cᵒᵖ ⥤ Type w}
    {F G : Cᵒᵖ ⥤ Type w} (φ : ∀ i, A i ⟶ F) (h : G ⟶ F)
    (hφ : ∀ (V : C) (x : F.obj (Opposite.op V)),
      (⨆ i, Presheaf.imageSieve (φ i) x) ∈ J V)
    (V : C) (s : G.obj (Opposite.op V)) :
    (⨆ i, Presheaf.imageSieve (Limits.pullback.fst h (φ i)) s) ∈ J V := by
  refine J.superset_covering ?_ (hφ V (h.app (Opposite.op V) s))
  rintro V' c hc
  simp only [iSup, Sieve.sSup_apply, Set.mem_range] at hc ⊢
  obtain ⟨-, ⟨i, rfl⟩, z, hz⟩ := hc
  have hcompat : h.app (Opposite.op V') (G.map c.op s) = (φ i).app (Opposite.op V') z := by
    rw [hz]
    exact h.naturality_apply c.op s
  have hpb := (IsPullback.of_hasPullback h (φ i)).map
    ((evaluation Cᵒᵖ (Type _)).obj (Opposite.op V'))
  obtain ⟨wv, hwv, -⟩ :=
    Types.exists_of_isPullback hpb (G.map c.op s) z hcompat
  exact ⟨_, ⟨i, rfl⟩, wv, hwv⟩

/-- **Composing a family with locally surjective morphisms does not change the covering
property of its image sieves.** If the image sieves of `{φᵢ : Aᵢ ⟶ F}` jointly cover at every
section and each `ψᵢ : Bᵢ ⟶ Aᵢ` is locally surjective, then the image sieves of
`{ψᵢ ≫ φᵢ}` jointly cover at every section: over an arrow of the first family's sieve the
section lifts to `Aᵢ`, and that lift is itself locally in the image of `ψᵢ`, so the local
character of the topology applies. -/
@[sga "3 IV 4.2.1" "more general", sga "3 IV 4.2.3" "special case"]
theorem imageSieve_iSup_mem_comp {ι : Type*} {A B' : ι → Cᵒᵖ ⥤ Type w}
    {F : Cᵒᵖ ⥤ Type w} (φ : ∀ i, A i ⟶ F) (ψ : ∀ i, B' i ⟶ A i)
    (hψ : ∀ i, Presheaf.IsLocallySurjective J (ψ i))
    (hφ : ∀ (V : C) (x : F.obj (Opposite.op V)),
      (⨆ i, Presheaf.imageSieve (φ i) x) ∈ J V)
    (V : C) (s : F.obj (Opposite.op V)) :
    (⨆ i, Presheaf.imageSieve (ψ i ≫ φ i) s) ∈ J V := by
  refine J.transitive (hφ V s) _ ?_
  rintro V' c hc
  simp only [iSup, Sieve.sSup_apply, Set.mem_range] at hc
  obtain ⟨-, ⟨i, rfl⟩, z, hz⟩ := hc
  have := hψ i
  refine J.superset_covering ?_ (Presheaf.imageSieve_mem J (ψ i) z)
  rintro V'' d ⟨y, hy⟩
  simp only [Sieve.pullback_apply, iSup, Sieve.sSup_apply, Set.mem_range]
  refine ⟨_, ⟨i, rfl⟩, y, ?_⟩
  show (ψ i ≫ φ i).app (Opposite.op V'') y = F.map (d ≫ c).op s
  rw [NatTrans.comp_app, types_comp_apply, hy, (φ i).naturality_apply d.op z, hz,
    ← Functor.map_comp_apply]
  rfl

end Sieves

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A base change of a morphism into a formal algebraic space receives a surjection from an
object of the site.** If `X` satisfies the set-theoretic condition of **Stacks 0AIS** and `Y` is
a formal algebraic space over `S`, then for every scheme-valued point `ξ : T ⟶ Y` the base
change `T ×_Y X` receives a locally surjective morphism from the universe-lifted Yoneda
presheaf of an object of the site.

The set-theoretic condition supplies an object `U_X` of the site and a locally surjective
`h_{U_X} ⟶ X`; the base change of that morphism along `T ×_Y X ⟶ X` is still locally
surjective, and it is the fibre product `h_T ×_Y h_{U_X}` of two scheme-valued points of `Y`,
which the representability assertion of **Stacks 0AIP**
(`AlgebraicGeometry.FormalSpace.essImage_pullback_of_isFormalAlgebraicSpace`) puts inside the
site. -/
theorem exists_representable_locallySurjective_pullback {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : SatisfiesSetTheoreticCondition B S hS X)
    (hY : IsFormalAlgebraicSpace B S hS Y)
    (T : BigFppfOver B S hS) (ξ : uliftYoneda.{u + 1}.obj T ⟶ Y.obj) :
    ∃ (W : BigFppfOver B S hS) (t : uliftYoneda.{u + 1}.obj W ⟶ pullback ξ f.hom),
      Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) t := by
  let : HasBinaryProducts (BigFppfOver B S hS) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  obtain ⟨UX, -, hUX, -, ⟨eU⟩, -, tX, htX, -⟩ := hX
  let t' : uliftYoneda.{u + 1}.obj UX ⟶ X.obj := eU.inv ≫ tX.hom
  have ht' : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) t' := by
    let : Sheaf.IsLocallySurjective tX := (Sheaf.isLocallySurjective_iff_epi tX).mpr htX
    dsimp only [t']
    infer_instance
  obtain ⟨W, ⟨e⟩⟩ :=
    essImage_pullback_of_isFormalAlgebraicSpace B S hS hY T UX ξ (t' ≫ f.hom)
  refine ⟨W, e.hom ≫ (pullbackLeftPullbackSndIso ξ f.hom t').inv ≫
    pullback.fst (pullback.snd ξ f.hom) t', ?_⟩
  have := ht'
  have : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
      (pullback.fst (pullback.snd ξ f.hom) t') :=
    Presheaf.isLocallySurjective_pullback_fst _ _ _
  infer_instance

/-- **A jointly surjective family of étale charts of a sheaf covered by one object of the site
can be replaced by a single chart.** Let `E` be an fppf sheaf receiving a locally surjective
morphism `t : h_{W'} ⟶ E` from the universe-lifted Yoneda presheaf of an object of the site,
and let `{gᵢ : h_{Zᵢ} ⟶ E}` be a family which is representable by objects of the site and
étale and whose image sieves jointly cover at every section of `E`. Then there are one object
`Z` of the site and one morphism `q : h_Z ⟶ E` with the same three properties —
representable by objects of the site, surjective, étale.

Moreover `q` inherits from the family every property of morphisms of schemes which is
Zariski-local at the source: if `π : E ⟶ h_T` is a morphism to an object of the site and each
`Zᵢ ⟶ T` induced by `gᵢ ≫ π` has such a property `P`, then so does the morphism `Z ⟶ T`
induced by `q ≫ π`. This is how a property of a morphism being descended along the family —
local finite type, for Stacks 0ANL — is carried to the single chart; the chart itself is
produced with no hypothesis of that kind, which is what makes it available to Stacks 0AN4,
where only representability is in play.

One member of the family is kept for each point of `W'`, and inside it an affine open around a
chosen preimage of that point: an *affine* chart of `E` is no larger than `W'` by
`AlgebraicGeometry.FormalSpace.affineChart_size_le'`, a scheme has at most `2 ^ size` points,
and the cutoff of the site is a strong prelimit, so the surviving family is indexed and sized
below the cutoff. `AlgebraicGeometry.FormalSpace.exists_chart_of_size_le` glues it, its
coproduct injections being open immersions which cover; local surjectivity of the glued
morphism comes from `CategoryTheory.Presheaf.isLocallySurjective_sigmaDesc_of_fac`, whose
commuting squares are the fibre products in the site of the chosen affine opens with the base
changes of the members along `t`; étaleness is
`AlgebraicGeometry.FormalSpace.etale_of_openCover`. -/
theorem exists_chart_of_etaleChartFamily {E : FppfSheaf B S hS}
    {W' : BigFppfOver B S hS} (t : uliftYoneda.{u + 1}.obj W' ⟶ E.obj)
    (ht : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) t)
    {I : Type (u + 1)} {Zt : I → BigFppfOver B S hS}
    (g : ∀ i, uliftYoneda.{u + 1}.obj (Zt i) ⟶ E.obj)
    (hge : ∀ i, (Space.etaleOnSite B S hS).relative uliftYoneda.{u + 1} (g i))
    (hgsieve : ∀ (V : BigFppfOver B S hS) (s : E.obj.obj (Opposite.op V)),
      (⨆ i, Presheaf.imageSieve (g i) s) ∈ BigFppfOver.topology B S hS V) :
    ∃ (Z : BigFppfOver B S hS) (q : uliftYoneda.{u + 1}.obj Z ⟶ E.obj),
      (Space.surjectiveOnSite B S hS).relative uliftYoneda.{u + 1} q ∧
      (Space.etaleOnSite B S hS).relative uliftYoneda.{u + 1} q ∧
      ∀ (T : BigFppfOver B S hS) (π : E.obj ⟶ uliftYoneda.{u + 1}.obj T)
        (P : MorphismProperty Scheme.{u}), IsZariskiLocalAtSource P →
        (∀ i, P ((BigFppfOver.toScheme B S hS).map
          (uliftYoneda.{u + 1}.preimage (g i ≫ π)))) →
        P ((BigFppfOver.toScheme B S hS).map (uliftYoneda.{u + 1}.preimage (q ≫ π))) := by
  classical
  let : MorphismProperty.RespectsIso (@AlgebraicGeometry.Etale.{u}) := .mk _
    (fun e f hf => by let := hf; infer_instance)
    (fun e f hf => by let := hf; infer_instance)
  let : (Space.etaleOnSite B S hS).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  let : MorphismProperty.IsStableUnderBaseChange (@AlgebraicGeometry.Etale.{u}) :=
    Etale.etale_isStableUnderBaseChange
  let : (Space.etaleOnSite B S hS).IsStableUnderComposition :=
    { comp_mem := fun f₁ f₂ h₁ h₂ => by
        have _ : Etale ((BigFppfOver.toScheme B S hS).map f₁) := h₁
        have _ : Etale ((BigFppfOver.toScheme B S hS).map f₂) := h₂
        show Etale ((BigFppfOver.toScheme B S hS).map (f₁ ≫ f₂))
        rw [Functor.map_comp]
        infer_instance }
  -- the base changes of the members along `t`, and the points of `W'` they meet
  have hqqet : ∀ i, Etale ((BigFppfOver.toScheme B S hS).map ((hge i).rep.snd t)) := fun i =>
    (hge i).property_snd t
  have hpoint : ∀ x : (BigFppfOver.toScheme B S hS).obj W',
      ∃ i, x ∈ Set.range ((BigFppfOver.toScheme B S hS).map ((hge i).rep.snd t)) := by
    intro x
    have hmem := hgsieve W' (uliftYonedaEquiv t)
    rw [GrothendieckTopology.mem_over_iff] at hmem
    obtain ⟨Ec, hEc, hEcR⟩ := AlgebraicGeometry.Space.exists_covering_refining_sieve B hmem
    have hEF := B.isFppfCovering_of_isCovering hEc
    rw [AlgebraicGeometry.IsFppfCovering, Precoverage.mem_comap_iff,
      PreZeroHypercover.presieve₀, Presieve.map_ofArrows,
      Scheme.fppfPrecoverage, Scheme.ofArrows_mem_precoverage_iff] at hEF
    obtain ⟨j, y, hy⟩ := hEF.1 x
    have hb := (Sieve.overEquiv_iff _ _).mp (hEcR _ _ ⟨j⟩)
    change (⨆ i, Presheaf.imageSieve (g i) (uliftYonedaEquiv t))
      (Over.homMk (Ec.f j) : Over.mk (Ec.f j ≫ W'.hom) ⟶ W') at hb
    simp only [iSup, Sieve.sSup_apply, Set.mem_range] at hb
    obtain ⟨-, ⟨i, rfl⟩, z, hz⟩ := hb
    have hw : (uliftYonedaEquiv.symm z :
          uliftYoneda.{u + 1}.obj (Over.mk (Ec.f j ≫ W'.hom)) ⟶
            uliftYoneda.{u + 1}.obj (Zt i)) ≫ g i =
        uliftYoneda.{u + 1}.map
          (Over.homMk (Ec.f j) : Over.mk (Ec.f j ≫ W'.hom) ⟶ W') ≫ t := by
      apply uliftYonedaEquiv.injective
      rw [uliftYonedaEquiv_comp, Equiv.apply_symm_apply]
      exact hz.trans (uliftYonedaEquiv_naturality.{u + 1} t _)
    have hl : uliftYoneda.{u + 1}.preimage (((hge i).rep.isPullback t).lift _ _ hw) ≫
          (hge i).rep.snd t =
        (Over.homMk (Ec.f j) : Over.mk (Ec.f j ≫ W'.hom) ⟶ W') := by
      apply uliftYoneda.{u + 1}.map_injective
      rw [Functor.map_comp, Functor.map_preimage]
      exact ((hge i).rep.isPullback t).lift_snd _ _ hw
    refine ⟨i, (BigFppfOver.toScheme B S hS).map
      (uliftYoneda.{u + 1}.preimage (((hge i).rep.isPullback t).lift _ _ hw)) y, ?_⟩
    rwa [← Scheme.Hom.comp_apply, ← Functor.map_comp, hl]
  choose idx hidx using hpoint
  -- an affine open of the chosen member around a chosen preimage of the point
  have hchoice : ∀ x : (BigFppfOver.toScheme B S hS).obj W',
      ∃ (A : ((BigFppfOver.toScheme B S hS).obj (Zt (idx x))).affineOpens)
        (z : (BigFppfOver.toScheme B S hS).obj ((hge (idx x)).rep.pullback t)) (a : A.1),
        (BigFppfOver.toScheme B S hS).map ((hge (idx x)).rep.snd t) z = x ∧
        A.1.ι a = (BigFppfOver.toScheme B S hS).map ((hge (idx x)).rep.fst' t) z := by
    intro x
    obtain ⟨z, hz⟩ := hidx x
    obtain ⟨A, hA, hzA, -⟩ := exists_isAffineOpen_mem_and_subset
      (X := (BigFppfOver.toScheme B S hS).obj (Zt (idx x)))
      (x := (BigFppfOver.toScheme B S hS).map ((hge (idx x)).rep.fst' t) z) (U := ⊤) trivial
    exact ⟨⟨A, hA⟩, z, ⟨_, hzA⟩, hz, by simp⟩
  choose Aff pz pt hpzq hpt using hchoice
  have hoiAff : ∀ x : (BigFppfOver.toScheme B S hS).obj W',
      AlgebraicGeometry.IsOpenImmersion (Aff x).1.ι := fun _ => inferInstance
  let V := fun x : (BigFppfOver.toScheme B S hS).obj W' =>
    Space.openSubobject B S hS (Zt (idx x)) (Aff x).1.ι (hoiAff x)
  let k : ∀ x, V x ⟶ Zt (idx x) := fun x =>
    Space.openSubobjectHom B S hS (Zt (idx x)) (Aff x).1.ι (hoiAff x)
  have hkxmap : ∀ x, (BigFppfOver.toScheme B S hS).map (k x) = (Aff x).1.ι := fun x =>
    Space.toScheme_map_openSubobjectHom B S hS (Zt (idx x)) (Aff x).1.ι (hoiAff x)
  have hkxoi : ∀ x, AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (k x)) :=
    fun x => by rw [hkxmap x]; exact hoiAff x
  have hfxe : ∀ x, (Space.etaleOnSite B S hS).relative uliftYoneda.{u + 1}
      (uliftYoneda.{u + 1}.map (k x) ≫ g (idx x)) := fun x => by
    have := hkxoi x
    exact MorphismProperty.comp_mem _ _ _
      (Space.relative_uliftYoneda_map B S hS _ _ inferInstance) (hge (idx x))
  have hsizeV : ∀ x, ((BigFppfOver.toScheme B S hS).obj (V x)).size ≤
      ((BigFppfOver.toScheme B S hS).obj W').size := fun x => by
    have : IsAffine (V x).left.obj := (Aff x).2
    exact affineChart_size_le' B S hS W' (V x) t ht _
      (MorphismProperty.relative_monotone
        (inverseImage_etale_le_locallyOfFiniteType B S hS) _ (hfxe x))
  have hμ : (2 : Cardinal.{u}) ^ ((BigFppfOver.toScheme B S hS).obj W').size < B.cutoff :=
    B.cutoff_isStrongPrelimit W'.left.property
  obtain ⟨Wc, kk, qc, hkq, hopenk, hcovk, hqrep⟩ :=
    exists_chart_of_size_le B S hS (X := E) V
      (fun x => uliftYoneda.{u + 1}.map (k x) ≫ g (idx x)) (fun x => (hfxe x).rep) hμ
      (mk_scheme_le_two_power_size _) fun x => (hsizeV x).trans (Cardinal.cantor _).le
  -- local surjectivity of the glued morphism
  have hsq : ∀ x, uliftYoneda.{u + 1}.map (pullback.fst (k x) ((hge (idx x)).rep.fst' t)) ≫
      (uliftYoneda.{u + 1}.map (k x) ≫ g (idx x)) =
      uliftYoneda.{u + 1}.map (pullback.snd (k x) ((hge (idx x)).rep.fst' t) ≫
        (hge (idx x)).rep.snd t) ≫ t := fun x => by
    rw [← Category.assoc, ← Functor.map_comp, pullback.condition, Functor.map_comp,
      Functor.map_comp, Category.assoc, Category.assoc,
      (hge (idx x)).rep.map_fst' t, ((hge (idx x)).rep.isPullback t).w]
  have hgqet : ∀ x, Etale (pullback.snd (k x) ((hge (idx x)).rep.fst' t) ≫
      (hge (idx x)).rep.snd t).left.hom := fun x => by
    have := hkxoi x
    have : Etale ((BigFppfOver.toScheme B S hS).map
        (pullback.snd (k x) ((hge (idx x)).rep.fst' t))) :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback
        ((IsPullback.of_hasPullback (k x) ((hge (idx x)).rep.fst' t)).map
          (BigFppfOver.toScheme B S hS)) inferInstance
    exact MorphismProperty.comp_mem (Space.etaleOnSite B S hS) _ _ this (hqqet (idx x))
  have hgqcov : ∀ x : (BigFppfOver.toScheme B S hS).obj W', ∃ x',
      x ∈ Set.range ((BigFppfOver.toScheme B S hS).map
        (pullback.snd (k x') ((hge (idx x')).rep.fst' t) ≫ (hge (idx x')).rep.snd t)) := by
    intro x
    have hpbsq := (IsPullback.of_hasPullback (k x) ((hge (idx x)).rep.fst' t)).map
      (BigFppfOver.toScheme B S hS)
    obtain ⟨v, -, hv⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := (BigFppfOver.toScheme B S hS).map (k x))
      (g := (BigFppfOver.toScheme B S hS).map ((hge (idx x)).rep.fst' t))
      (pt x) (pz x) (by rw [hkxmap x]; exact hpt x)
    have h1 : ((BigFppfOver.toScheme B S hS).map
        (pullback.snd (k x) ((hge (idx x)).rep.fst' t))) (hpbsq.isoPullback.inv v) = pz x := by
      rw [← Scheme.Hom.comp_apply, hpbsq.isoPullback_inv_snd]
      exact hv
    refine ⟨x, hpbsq.isoPullback.inv v, ?_⟩
    rw [Functor.map_comp, Scheme.Hom.comp_apply, h1]
    exact hpzq x
  have hu : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
      (Sigma.desc fun x => uliftYoneda.{u + 1}.map (pullback.snd (k x)
        ((hge (idx x)).rep.fst' t) ≫ (hge (idx x)).rep.snd t)) :=
    ((BigFppfOver.topology B S hS).ofArrows_mem_iff_isLocallySurjective_sigmaDesc_uliftYoneda_map
      _).mp
      (fppf_ofArrows_mem B S hS _ _
        (fun x => by have := hgqet x; infer_instance)
        (fun x => by have := hgqet x; infer_instance) hgqcov)
  have hfxls := Presheaf.isLocallySurjective_sigmaDesc_of_fac
    (BigFppfOver.topology B S hS) _ _ _ t hu ht hsq
  have hcomp : (Sigma.desc fun x => uliftYoneda.{u + 1}.map (kk x)) ≫ qc =
      Sigma.desc fun x => uliftYoneda.{u + 1}.map (k x) ≫ g (idx x) := by
    refine Sigma.hom_ext _ _ fun x => ?_
    rw [← Category.assoc, Sigma.ι_desc, Sigma.ι_desc, hkq x]
  have : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
      ((Sigma.desc fun x => uliftYoneda.{u + 1}.map (kk x)) ≫ qc) := by
    rw [hcomp]; exact hfxls
  have hqls : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) qc :=
    Presheaf.isLocallySurjective_of_isLocallySurjective (BigFppfOver.topology B S hS)
      (Sigma.desc fun x => uliftYoneda.{u + 1}.map (kk x)) qc
  refine ⟨Wc, qc, relative_surjective_of_locallySurjective B S hS qc hqrep hqls,
    etale_of_openCover B S hS _ kk hopenk hcovk qc hqrep
      (fun x => by rw [hkq x]; exact hfxe x), ?_⟩
  -- a property Zariski-local at the source passes from the members to the glued morphism
  intro T π P hPzar hwP
  let := hPzar
  have hkkwc : ∀ x, kk x ≫ uliftYoneda.{u + 1}.preimage (qc ≫ π) =
      k x ≫ uliftYoneda.{u + 1}.preimage (g (idx x) ≫ π) := fun x => by
    apply uliftYoneda.{u + 1}.map_injective
    rw [Functor.map_comp, Functor.map_comp, uliftYoneda.{u + 1}.map_preimage,
      ← Category.assoc, hkq x, Category.assoc, uliftYoneda.{u + 1}.map_preimage]
  refine IsZariskiLocalAtSource.of_openCover (P := P)
    { I₀ := _
      X := fun x => (BigFppfOver.toScheme B S hS).obj (V x)
      f := fun x => (BigFppfOver.toScheme B S hS).map (kk x)
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        exact ⟨hcovk, hopenk⟩ } fun x => ?_
  show P ((BigFppfOver.toScheme B S hS).map (kk x) ≫
    (BigFppfOver.toScheme B S hS).map (uliftYoneda.{u + 1}.preimage (qc ≫ π)))
  rw [← Functor.map_comp, hkkwc x, Functor.map_comp, hkxmap x]
  exact IsZariskiLocalAtSource.comp (hwP (idx x)) (Aff x).1.ι

/-- **A chart of every base change, from a jointly surjective étale family which is locally of
finite type over the target.** Let `f : X ⟶ Y` be a morphism of fppf sheaves on the big fppf
site of `S` with `X` satisfying the set-theoretic condition of **Stacks 0AIS** and `Y` a formal
algebraic space over `S`, and let `{pᵢ : Uᵢ ⟶ X}` be a jointly surjective family of
representable étale morphisms each of whose composites with `f` is locally of finite type. Then
every scheme-valued point `ξ : T ⟶ Y` of the target admits an object `Z` of the site and a
morphism `q : h_Z ⟶ T ×_Y X` which is representable by objects of the site, surjective and
étale, and whose composite with the projection to `T` is a morphism `Z ⟶ T` of the site locally
of finite type.

The member charts are
`AlgebraicGeometry.FormalSpace.exists_memberChart_pullback`, their image sieves jointly cover by
the two sieve lemmas above, the surjection from an object of the site is
`AlgebraicGeometry.FormalSpace.exists_representable_locallySurjective_pullback`, and the family
is cut down and glued by
`AlgebraicGeometry.FormalSpace.exists_chart_of_etaleChartFamily`. The local finite type
condition carried by `pᵢ ≫ f` is what makes each member chart locally of finite type over `T`,
and the glued chart inherits it because being locally of finite type is Zariski-local at the
source. -/
theorem exists_schemeChart_pullback_of_etaleFamily {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : SatisfiesSetTheoreticCondition B S hS X)
    (hY : IsFormalAlgebraicSpace B S hS Y)
    {I : Type (u + 1)} {U : I → FppfSheaf B S hS} (p : ∀ i, U i ⟶ X)
    (hp : ∀ i, IsRepresentableEtale B S hS (p i))
    (hcov : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
        Sheaf.instHasColimitsOfSize
      Sheaf.IsLocallySurjective (Sigma.desc p))
    (hlft : ∀ i, IsLocallyOfFiniteType B S hS (p i ≫ f))
    (T : BigFppfOver B S hS) (ξ : uliftYoneda.{u + 1}.obj T ⟶ Y.obj) :
    ∃ (Z : BigFppfOver B S hS) (w : Z ⟶ T)
      (q : uliftYoneda.{u + 1}.obj Z ⟶ pullback ξ f.hom),
      q ≫ pullback.fst ξ f.hom = uliftYoneda.{u + 1}.map w ∧
      (Space.surjectiveOnSite B S hS).relative uliftYoneda.{u + 1} q ∧
      (Space.etaleOnSite B S hS).relative uliftYoneda.{u + 1} q ∧
      LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map w) := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  have hEsheaf : Presheaf.IsSheaf (BigFppfOver.topology B S hS) (pullback ξ f.hom) :=
    Presheaf.isSheaf_pullback _ ξ f.hom
      (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS T).isSheaf X.property Y.property
  choose Zt β hβS hβE hge using fun i =>
    exists_memberChart_pullback B S hS f (p i) (hp i) (hlft i).1 T ξ
  -- each member chart is locally of finite type over `T`
  have hwlft : ∀ i, LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map
      (uliftYoneda.{u + 1}.preimage
        ((β i ≫ pullback.fst (pullback.snd ξ f.hom) (p i).hom) ≫ pullback.fst ξ f.hom))) := by
    intro i
    have hfac : pullback.fst (pullback.snd ξ f.hom) (p i).hom ≫ pullback.fst ξ f.hom =
        (pullbackLeftPullbackSndIso ξ f.hom (p i).hom).hom ≫
          pullback.fst ξ ((p i).hom ≫ f.hom) := by
      simp
    have hlftu : Space.IsLocallyOfFiniteTypeULift.{u + 1} B S hS
        (pullback.fst (pullback.snd ξ f.hom) (p i).hom ≫ pullback.fst ξ f.hom) := by
      rw [hfac]
      exact Space.holdsOnEveryEtaleChartULift_precomp B S hS
        (@AlgebraicGeometry.LocallyOfFiniteType.{u}) _ _ ((hlft i).2 T ξ)
    refine hlftu (Zt i) T (β i) (𝟙 _) _ (hβE i)
      (Space.relative_id_etale.{u + 1} B S hS T) ?_
    rw [Category.comp_id, Functor.map_preimage, Category.assoc]
  obtain ⟨W', t, ht⟩ := exists_representable_locallySurjective_pullback B S hS f hX hY T ξ
  obtain ⟨Z, q, hqs, hqe, hqP⟩ := exists_chart_of_etaleChartFamily B S hS
    (E := (⟨pullback ξ f.hom, hEsheaf⟩ : FppfSheaf B S hS)) t ht
    (fun i => β i ≫ pullback.fst (pullback.snd ξ f.hom) (p i).hom) hge
    (imageSieve_iSup_mem_comp (BigFppfOver.topology B S hS)
      (fun i => pullback.fst (pullback.snd ξ f.hom) (p i).hom) β
      (fun i => isLocallySurjective_of_relative_surjective_etale B S hS (β i) (hβS i) (hβE i))
      (imageSieve_iSup_mem_pullback_fst (BigFppfOver.topology B S hS)
        (fun i => (p i).hom) (pullback.snd ξ f.hom)
        (fun V x => family_imageSieve_mem (BigFppfOver.topology B S hS) U X p hcov V x)))
  exact ⟨Z, uliftYoneda.{u + 1}.preimage (q ≫ pullback.fst ξ f.hom), q,
    (uliftYoneda.{u + 1}.map_preimage _).symm, hqs, hqe,
    hqP T (pullback.fst ξ f.hom) (@AlgebraicGeometry.LocallyOfFiniteType.{u})
      (HasRingHomProperty.instIsZariskiLocalAtSource
        (P := @AlgebraicGeometry.LocallyOfFiniteType.{u})) hwlft⟩

/-- **Being locally of finite type is local on the source, along a jointly surjective étale
family.** Let `f : X ⟶ Y` be a morphism of fppf sheaves on the big fppf site of `S` with `X`
satisfying the set-theoretic condition of **Stacks 0AIS** and `Y` a formal algebraic space over
`S`. If `{pᵢ : Uᵢ ⟶ X}` is a family of representable étale morphisms which is jointly surjective
as a family of morphisms of sheaves and each composite `pᵢ ≫ f` is locally of finite type, then
`f` is locally of finite type.

Nothing is asked of the sources `Uᵢ` beyond the sheaf condition, and the conclusion is the full
condition of Stacks 0AM4 for `f`, representability included. Both halves are read at one
scheme-valued point `ξ : T ⟶ Y` of the target and both come from the single chart of
`AlgebraicGeometry.FormalSpace.exists_schemeChart_pullback_of_etaleFamily`: representability is
**Stacks 0BGR** applied to that chart, and the local finite type condition is **Stacks 03MJ**
applied to it together with the identity of `T`.

This is the family form of
`AlgebraicGeometry.FormalSpace.IsLocallyOfFiniteType.of_comp_of_locallySurjective`, which
consumes a single surjective representable étale morphism. The coproduct of the family is of no
use in its place: a coproduct of algebraic spaces over an index type of `Type (u + 1)` need not
be an algebraic space over `S`, the disjoint union of their scheme atlases being inside the site
only under a uniform size bound. -/
theorem IsLocallyOfFiniteType.of_etaleFamily {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : SatisfiesSetTheoreticCondition B S hS X)
    (hY : IsFormalAlgebraicSpace B S hS Y)
    {I : Type (u + 1)} {U : I → FppfSheaf B S hS} (p : ∀ i, U i ⟶ X)
    (hp : ∀ i, IsRepresentableEtale B S hS (p i))
    (hcov : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
        Sheaf.instHasColimitsOfSize
      Sheaf.IsLocallySurjective (Sigma.desc p))
    (hlft : ∀ i, IsLocallyOfFiniteType B S hS (p i ≫ f)) :
    IsLocallyOfFiniteType B S hS f := by
  have hchart := fun (T : BigFppfOver B S hS) (ξ : uliftYoneda.{u + 1}.obj T ⟶ Y.obj) =>
    exists_schemeChart_pullback_of_etaleFamily B S hS f hX hY p hp hcov hlft T ξ
  have hrepf : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom := by
    intro T ξ
    obtain ⟨Z, -, q, -, hqs, hqe, -⟩ := hchart T ξ
    exact Space.isAlgebraicSpaceULift_of_relative_surjective_etale B S hS
      (Presheaf.isSheaf_pullback _ ξ f.hom
        (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS T).isSheaf X.property Y.property)
      (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS Z) q hqs hqe
  refine ⟨hrepf, fun T ξ => ?_⟩
  show Space.IsLocallyOfFiniteTypeULift.{u + 1} B S hS (pullback.fst ξ f.hom)
  obtain ⟨Z, w, q, hfac, hqs, hqe, hwlft⟩ := hchart T ξ
  refine Space.holdsOnEveryEtaleChartULift_of_surjectiveChart B S hS
    (@AlgebraicGeometry.LocallyOfFiniteType.{u})
    LocallyOfFiniteType.isEtaleLocalOnSourceAndTarget (hrepf T ξ)
    (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS T) Z T q (𝟙 _) w hqe
    (Space.relative_id_etale.{u + 1} B S hS T) hqs ?_ hwlft
  rw [Category.comp_id]
  exact hfac.symm

end AlgebraicGeometry.FormalSpace



end
