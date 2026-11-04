module

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.BlowUpFreePullbackSectionShrink
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.BlowUpFreeChartOverlapBridge

/-!
# The chart comparison over the preimage of a trivialising open, shrunk

The comparison `b^*N ≅ 𝒢` of the essential surjectivity half of [Stacks, Tag 0EXD] is glued from
the two chart comparisons `AlgebraicGeometry.preimageChartIso` by
`Stacks.AlgebraicGeometry.ModuleLimits.nonempty_iso_of_cover_of_inf`, which asks for its local
data to agree on the pairwise intersections *as morphisms of restrictions*, in the sectionwise
spelling `Stacks.AlgebraicGeometry.ModuleLimits.restrictHomOfLE`.  This file puts the free chart
into that shape.

Two steps are needed, and they are independent of each other.

The first is the passage from the sectionwise spelling to the chart calculus:
`AlgebraicGeometry.restrictHomOfLE_iso_hom` says that restricting an *isomorphism* of
restrictions to a smaller open is its chart comparison followed by the comparison of the two
restrictions of the target.  So an equation of the form
`restrictChartIso … ≪≫ (restrictCompIso …).symm = …`, which is how both chart shrinks of this
development are stated, becomes an equation between `restrictHomOfLE`s by taking
`CategoryTheory.Iso.hom`.

The second is the shrink of the free chart itself.  `AlgebraicGeometry.pullbackFreeChartCompIso`
is, by `AlgebraicGeometry.pullbackFreeChartCompIso_eq`, a pair of trivialisations by one free
module:  the trivialisation of `b^*N`, which shrinks by
`AlgebraicGeometry.restrictChartIso_pullbackFreeTrivIso`, and the trivialisation of `𝒢` given by
`α`, which shrinks by `AlgebraicGeometry.restrictChartIso_freeChartTargetIso`.  A comparison
presented that way shrinks as soon as both of its trivialisations do, the free comparison
cancelling between them -- that is
`Stacks.AlgebraicGeometry.ModuleLimits.trivPair_shrink`, and
`AlgebraicGeometry.restrictChartIso_pullbackFreeChartCompIso` is its instance.  The result has
exactly the shape of `AlgebraicGeometry.restrictChartIso_pullbackSectionChartIso`, so the two
charts of the descent are now shrunk uniformly.

The file then records the one further identity the *agreement* of the two charts over the overlap
rests on, as opposed to their shrinks:  over the overlap the free chart trivialises `𝒢` by `α`
over `b ⁻¹ᵁ (U ⊓ V)` directly, whereas the section chart trivialises it by `α` along the section
and pulls that back.  `AlgebraicGeometry.pullbackRestrictObjIso_hom_eq_of_isIso` says the two
agree:  the trivialisation by `α` along an open immersion `p`, pulled back along `g` and read
through the two free comparisons, is the structural comparison
`AlgebraicGeometry.pullbackRestrictObjIso` for `g ≫ p`.  It holds for any `α` invertible after
restriction along `p`, and nothing about the blow-up enters.

## Implementation notes

`Stacks.AlgebraicGeometry.ModuleLimits.trivPair_shrink` is stated over abstract categories, like
`Stacks.AlgebraicGeometry.ModuleLimits.trivShrink_of_paste` before it and for the same reason.
The instance needed here has a free module on a scheme as its trivialising object, and at those
types `AlgebraicGeometry.Scheme.ringCatSheaf` does not unfold at the transparency `rw` and `simp`
build their motives at, so no rewrite fires.  Stated over variables the proof is four rewrites.

For the same reason `AlgebraicGeometry.pullbackRestrictObjIso_free` and
`AlgebraicGeometry.pullbackRestrictObjIso_hom_eq_of_isIso` are term mode, while
`AlgebraicGeometry.pullbackRestrictObjIso_naturality`, which mentions no free module, is an
ordinary rewrite proof.

## Main results

* `Stacks.AlgebraicGeometry.ModuleLimits.trivPair_shrink`: **a comparison presented as a pair of
  trivialisations shrinks as soon as both trivialisations do.**
* `AlgebraicGeometry.restrictHomOfLE_iso_hom`: the sectionwise restriction of an isomorphism of
  restrictions is its chart comparison, conjugated.
* `AlgebraicGeometry.restrictChartIso_pullbackFreeChartCompIso`: **the chart comparison over the
  preimage of an open on which `N` is trivialised is compatible with shrinking the open.**
* `AlgebraicGeometry.pullbackRestrictObjIso_naturality`, and
  `AlgebraicGeometry.pullbackRestrictObjIso_free`: the structural comparison is natural, and at a
  free module it is the pulled-back free comparison.
* `AlgebraicGeometry.pullbackRestrictObjIso_hom_eq_of_isIso`: **the trivialisation of `𝒢` by `α`
  is compatible with inverse images.**

## References

* [Stacks Project, Tag 0EXD](https://stacks.math.columbia.edu/tag/0EXD)
* [Stacks Project, Tag 0EVH](https://stacks.math.columbia.edu/tag/0EVH)
* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u v₁ v₂ w₁ w₂

namespace Stacks.AlgebraicGeometry.ModuleLimits

/-- **A comparison presented as a pair of trivialisations shrinks, given that each of the two
trivialisations shrinks.**

`rcM` and `rcG` are the two comparisons of a restriction along a composite with the iterated
restriction, `P` and `Q` the two trivialisations over the larger open and `P2`, `Q2` those over
the smaller one, and `R` the comparison of the restriction of the trivialising object with the
trivialising object over the smaller open.  The two hypotheses are that `P` shrinks to `P2` and
`Q` to `Q2`; the conclusion is that the comparison `P ≪≫ Q.symm` shrinks to `P2 ≪≫ Q2.symm`, the
factor `R` cancelling.

It is stated over abstract categories because at the chart comparison of the blow-up descent the
trivialising object is a free module on a scheme, and at those types no rewrite fires -- see the
implementation notes of
`StacksFrontier/AlgebraicGeometry/FiniteLocallyFree/BlowUpFreePullbackChartShrink.lean`. -/
theorem trivPair_shrink {𝒞 : Type w₁} {𝒟 : Type w₂} [Category.{v₁} 𝒞] [Category.{v₂} 𝒟]
    (F : 𝒞 ⥤ 𝒟) {Mk Gk Fr' : 𝒟} {Mp Gp Fr : 𝒞} (rcM : Mk ≅ F.obj Mp) (rcG : Gk ≅ F.obj Gp)
    (P : Mp ≅ Fr) (Q : Gp ≅ Fr) (P2 : Mk ≅ Fr') (Q2 : Gk ≅ Fr') (R : F.obj Fr ≅ Fr')
    (hP : rcM ≪≫ F.mapIso P = P2 ≪≫ R.symm)
    (hQ : rcG ≪≫ F.mapIso Q = Q2 ≪≫ R.symm) :
    rcM ≪≫ F.mapIso (P ≪≫ Q.symm) ≪≫ rcG.symm = P2 ≪≫ Q2.symm := by
  have hPh := congrArg Iso.hom hP
  have hQi := congrArg Iso.inv hQ
  refine Iso.ext ?_
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Functor.mapIso_hom,
    Functor.mapIso_inv, CategoryTheory.Functor.map_comp, Category.assoc] at hPh hQi ⊢
  rw [← Category.assoc rcM.hom (F.map P.hom), hPh, Category.assoc, hQi]
  simp

end Stacks.AlgebraicGeometry.ModuleLimits

namespace AlgebraicGeometry

/-- **A chart comparison restricted to a smaller open is the chart comparison of the restricted
trivialisation, conjugated by the comparison of the two restrictions of the target.**  This is
`Stacks.AlgebraicGeometry.ModuleLimits.restrictHomOfLE_chart_conj` with no morphism of
trivialised objects inserted:  the isomorphism `κ` itself is restricted. -/
theorem restrictHomOfLE_iso_hom {X : Scheme.{u}} {M N : X.Modules} {P P' : X.Opens}
    (e : P' ≤ P) (κ : Scheme.Modules.restrict M P.ι ≅ Scheme.Modules.restrict N P.ι) :
    Stacks.AlgebraicGeometry.ModuleLimits.restrictHomOfLE e κ.hom =
      (restrictChartIso P.ι κ (X.homOfLE e) (Scheme.homOfLE_ι X e)).hom ≫
        (restrictCompIso (X.homOfLE e) P.ι (Scheme.homOfLE_ι X e) N).inv := by
  rw [Stacks.AlgebraicGeometry.ModuleLimits.restrictHomOfLE_eq_restrictLocal, restrictLocal_eq]
  simp only [restrictChartIso, Iso.trans_hom, Functor.mapIso_hom, Category.assoc]

/-! ### The trivialisation of `𝒢` by `α` is compatible with inverse images -/

/-- **`AlgebraicGeometry.pullbackRestrictObjIso` is natural in the module.**  Each of its three
factors is, so this is three naturalities in a row. -/
theorem pullbackRestrictObjIso_naturality {A B S : Scheme.{u}} (g : A ⟶ B) (p : B ⟶ S)
    [IsOpenImmersion p] {k : A ⟶ S} (hk : g ≫ p = k) [IsOpenImmersion k] {M M' : S.Modules}
    (φ : M ⟶ M') :
    (Scheme.Modules.pullback g).map ((Scheme.Modules.restrictFunctor p).map φ) ≫
        (pullbackRestrictObjIso g p hk M').hom =
      (pullbackRestrictObjIso g p hk M).hom ≫ (Scheme.Modules.restrictFunctor k).map φ := by
  have h1 := (Scheme.Modules.restrictFunctorIsoPullback p).hom.naturality φ
  have h2 := (modulesPullbackTriangleIso g p k hk).hom.naturality φ
  dsimp only [Functor.comp_map] at h2
  have h3 := (Scheme.Modules.restrictFunctorIsoPullback k).inv.naturality φ
  simp only [pullbackRestrictObjIso, pullbackCompIsoOfEq_eq, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Iso.app_hom, Iso.app_inv]
  rw [← CategoryTheory.Functor.map_comp_assoc, h1, CategoryTheory.Functor.map_comp,
    Category.assoc, reassoc_of% h2, h3]
  simp only [Category.assoc]

/-- **The free comparison of a restriction, pulled back, is
`AlgebraicGeometry.pullbackRestrictObjIso` at the free module.**  This is
`Stacks.Modules.pullback_map_restrictFreeIso_hom_comp_pullbackFreeIso_hom` with the free
comparison at the composite traded for the restriction one by
`Stacks.Modules.restrictFreeIso_eq`. -/
theorem pullbackRestrictObjIso_free {A B S : Scheme.{u}} (g : A ⟶ B) (p : B ⟶ S)
    [IsOpenImmersion p] {k : A ⟶ S} (hk : g ≫ p = k) [IsOpenImmersion k] (I : Type u) :
    (Scheme.Modules.pullback g).map (Stacks.Modules.restrictFreeIso p I).hom ≫
        (Scheme.Modules.pullbackFreeIso g I).hom ≫
          (Stacks.Modules.restrictFreeIso k I).inv =
      (pullbackRestrictObjIso g p hk
        (_root_.SheafOfModules.free (R := S.ringCatSheaf) I)).hom :=
  have hk2 : (Stacks.Modules.restrictFreeIso k I).inv =
      (Scheme.Modules.pullbackFreeIso k I).inv ≫
        (Scheme.Modules.restrictFunctorIsoPullback k).inv.app
          (_root_.SheafOfModules.free (R := S.ringCatSheaf) I) :=
    congrArg Iso.inv (Stacks.Modules.restrictFreeIso_eq k I)
  (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ (Stacks.Modules.restrictFreeIso k I).inv)
      (Stacks.Modules.pullback_map_restrictFreeIso_hom_comp_pullbackFreeIso_hom g p hk I)).trans
      ((Category.assoc _ _ _).trans
        (congrArg ((Scheme.Modules.pullback g).map
            ((Scheme.Modules.restrictFunctorIsoPullback p).hom.app
              (_root_.SheafOfModules.free (R := S.ringCatSheaf) I)) ≫ ·)
          ((Category.assoc _ _ _).trans
            (congrArg ((pullbackCompIsoOfEq g p hk
                (_root_.SheafOfModules.free (R := S.ringCatSheaf) I)).hom ≫ ·)
              ((congrArg ((Scheme.Modules.pullbackFreeIso k I).hom ≫ ·) hk2).trans
                ((Scheme.Modules.pullbackFreeIso k I).hom_inv_id_assoc _)))))))

variable {X X' : Scheme.{u}} (b : X' ⟶ X) {I : Type u} {G : X'.Modules}
  (α : _root_.SheafOfModules.free.{u} I ⟶ G)

/-- **The trivialisation of `𝒢` by `α` along an open immersion `p`, pulled back along `g` and read
through the two free comparisons, is the comparison
`AlgebraicGeometry.pullbackRestrictObjIso`.**

Read the other way round:  the restriction of `𝒢` along `g ≫ p` is identified with the inverse
image along `g` of its restriction along `p` *compatibly with the trivialisations `α` gives over
the two*.  This is what identifies the two chart comparisons of the blow-up descent over the
overlap:  there the free chart trivialises `𝒢` over `b ⁻¹ᵁ (U ⊓ V)` directly, while the section
chart trivialises it along the section and then pulls back.

The proof is the naturality
`AlgebraicGeometry.pullbackRestrictObjIso_naturality` at `α` together with
`AlgebraicGeometry.pullbackRestrictObjIso_free`; the two restrictions of `α` cancel against each
other. -/
theorem pullbackRestrictObjIso_hom_eq_of_isIso {A B : Scheme.{u}} (g : A ⟶ B) (p : B ⟶ X')
    [IsOpenImmersion p] {k : A ⟶ X'} (hk : g ≫ p = k) [IsOpenImmersion k]
    (hp : IsIso ((Scheme.Modules.restrictFunctor p).map α)) :
    (Scheme.Modules.pullback g).map (inv ((Scheme.Modules.restrictFunctor p).map α)) ≫
          (Scheme.Modules.pullback g).map (Stacks.Modules.restrictFreeIso p I).hom ≫
          (Scheme.Modules.pullbackFreeIso g I).hom ≫
          (Stacks.Modules.restrictFreeIso k I).inv ≫
          (Scheme.Modules.restrictFunctor k).map α =
      (pullbackRestrictObjIso g p hk G).hom :=
  have hBig : (Scheme.Modules.pullback g).map (Stacks.Modules.restrictFreeIso p I).hom ≫
        (Scheme.Modules.pullbackFreeIso g I).hom ≫
          (Stacks.Modules.restrictFreeIso k I).inv ≫
          (Scheme.Modules.restrictFunctor k).map α =
      (pullbackRestrictObjIso g p hk
          (_root_.SheafOfModules.free (R := X'.ringCatSheaf) I)).hom ≫
        (Scheme.Modules.restrictFunctor k).map α :=
    (congrArg ((Scheme.Modules.pullback g).map (Stacks.Modules.restrictFreeIso p I).hom ≫ ·)
      (Category.assoc _ _ _).symm).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ (Scheme.Modules.restrictFunctor k).map α)
          (pullbackRestrictObjIso_free g p hk I)))
  (congrArg ((Scheme.Modules.pullback g).map
      (inv ((Scheme.Modules.restrictFunctor p).map α)) ≫ ·)
    (hBig.trans (pullbackRestrictObjIso_naturality g p hk α).symm)).trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ (pullbackRestrictObjIso g p hk G).hom)
        ((((Scheme.Modules.pullback g).map_comp _ _).symm.trans
          (congrArg (Scheme.Modules.pullback g).map (IsIso.inv_hom_id _))).trans
          ((Scheme.Modules.pullback g).map_id _))).trans (Category.id_comp _)))

/-- **The chart comparison over the preimage of an open on which `N` is trivialised is compatible
with shrinking the open.**

This is the two shrinks of the two halves of
`AlgebraicGeometry.pullbackFreeChartCompIso_eq` put together by
`Stacks.AlgebraicGeometry.ModuleLimits.trivPair_shrink`:  the trivialisation of `b^*N` shrinks by
`AlgebraicGeometry.restrictChartIso_pullbackFreeTrivIso` and the trivialisation of `𝒢` by
`AlgebraicGeometry.restrictChartIso_freeChartTargetIso`, and the comparison of the two free
modules cancels between them.

The shape matches `AlgebraicGeometry.restrictChartIso_pullbackSectionChartIso` exactly, so taking
`CategoryTheory.Iso.hom` of either turns it into an equation between
`Stacks.AlgebraicGeometry.ModuleLimits.restrictHomOfLE`s. -/
theorem restrictChartIso_pullbackFreeChartCompIso {W W' : X.Opens} (hW : W' ≤ W)
    (N : X.Modules)
    (τ : Scheme.Modules.restrict N W.ι ≅
      _root_.SheafOfModules.free (R := W.toScheme.ringCatSheaf) I)
    (τ' : Scheme.Modules.restrict N W'.ι ≅
      _root_.SheafOfModules.free (R := W'.toScheme.ringCatSheaf) I)
    (hα : IsIso ((Scheme.Modules.restrictFunctor (b ⁻¹ᵁ W).ι).map α))
    (hα' : IsIso ((Scheme.Modules.restrictFunctor (b ⁻¹ᵁ W').ι).map α))
    (hτ : restrictChartIso W.ι τ (X.homOfLE hW) (Scheme.homOfLE_ι X hW) =
      τ' ≪≫ (Stacks.Modules.restrictFreeIso (X.homOfLE hW) I).symm) :
    restrictChartIso (b ⁻¹ᵁ W).ι (pullbackFreeChartCompIso b α W N τ hα)
            (X'.homOfLE (b.preimage_mono hW))
            (Scheme.homOfLE_ι X' (b.preimage_mono hW)) ≪≫
          (restrictCompIso (X'.homOfLE (b.preimage_mono hW)) (b ⁻¹ᵁ W).ι
            (Scheme.homOfLE_ι X' (b.preimage_mono hW)) G).symm =
      pullbackFreeChartCompIso b α W' N τ' hα' := by
  refine Eq.trans (congrArg (fun s₀ => restrictChartIso (b ⁻¹ᵁ W).ι s₀
        (X'.homOfLE (b.preimage_mono hW))
        (Scheme.homOfLE_ι X' (b.preimage_mono hW)) ≪≫
      (restrictCompIso (X'.homOfLE (b.preimage_mono hW)) (b ⁻¹ᵁ W).ι
        (Scheme.homOfLE_ι X' (b.preimage_mono hW)) G).symm)
    (pullbackFreeChartCompIso_eq b α W N τ hα)) ?_
  refine Eq.trans ?_ (pullbackFreeChartCompIso_eq b α W' N τ' hα').symm
  exact Stacks.AlgebraicGeometry.ModuleLimits.trivPair_shrink
    (Scheme.Modules.restrictFunctor (X'.homOfLE (b.preimage_mono hW)))
    (restrictCompIso (X'.homOfLE (b.preimage_mono hW)) (b ⁻¹ᵁ W).ι
      (Scheme.homOfLE_ι X' (b.preimage_mono hW)) ((Scheme.Modules.pullback b).obj N))
    (restrictCompIso (X'.homOfLE (b.preimage_mono hW)) (b ⁻¹ᵁ W).ι
      (Scheme.homOfLE_ι X' (b.preimage_mono hW)) G)
    (pullbackFreeTrivIso b W N τ) (freeChartTargetIso α (b ⁻¹ᵁ W) hα)
    (pullbackFreeTrivIso b W' N τ') (freeChartTargetIso α (b ⁻¹ᵁ W') hα')
    (Stacks.Modules.restrictFreeIso (X'.homOfLE (b.preimage_mono hW)) I)
    (restrictChartIso_pullbackFreeTrivIso b hW N τ τ' hτ)
    (restrictChartIso_freeChartTargetIso α (b.preimage_mono hW) hα hα')

end AlgebraicGeometry

end
