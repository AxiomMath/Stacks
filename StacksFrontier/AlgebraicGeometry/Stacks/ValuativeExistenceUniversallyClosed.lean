module

public import Mathlib.Tactic.CategoryTheory.Bicategory.Basic
public import Mathlib.Tactic.CategoryTheory.Reassoc
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.ValuativeSquareSpecialisation

/-!
# A quasi-separated universally closed morphism satisfies valuative existence (Stacks 0CLX)

Let `f : 𝒳 ⟶ 𝒴` be a quasi-separated, universally closed 1-morphism of algebraic stacks over `S`
and let `q` be a valuative square for it (**Stacks 0CLK**): a valuation ring `A = q.R` with
fraction field `K = q.K`, a generic point `Spec K ⟶ 𝒳`, a special point `Spec A ⟶ 𝒴` and a
2-morphism filling the square. This file produces the dominating extension and the dotted arrow
that **Stacks 0CLX** asserts to exist, which is the existence part of the valuative criterion.

The first paragraph of the source's proof is
`StacksFrontier.AlgebraicGeometry.Stacks.ValuativeSquareBaseChange` and its specialisation step is
`StacksFrontier.AlgebraicGeometry.Stacks.ValuativeSquareSpecialisation`: base changing `f` along the
special point turns the solid square into the *generic section* `Spec K ⟶ Spec A ×_𝒴 𝒳`, which is
quasi-compact, and the closure of its image meets the fibre over the closed point of `Spec A`, so
**Stacks 0CL2** supplies a valuative square `q₂` for the generic section itself. The dominating
valuation ring of Stacks 0CLX is `q₂.R` and the extension of the fraction field is `q₂.K`.

What this file adds is the passage from `q₂` back to the data Stacks 0CLK asks for.

## Main results

* `AlgebraicGeometry.Stack.valuativeCriterionExistence_of_universallyClosed`: **Stacks 0CLX**.

## Implementation notes

Three things carry the proof.

**The ring maps come from 2-Yoneda.** The special point of `q₂` composed with the projection to
`Spec A` is a 1-morphism between two *represented* categories fibred in groupoids, so it is
induced by a morphism of the big fppf category over `S`
(`AlgebraicGeometry.Stack.schemeMapOfFunctor`), whose underlying morphism of schemes is a morphism
of spectra of rings and therefore `Spec` of a ring map, `Spec` being fully faithful. That is
`AlgebraicGeometry.Stack.ValuativeSquare.ringMapOfGenericSection`; the generic point of `q₂` gives
`fieldMapOfGenericSection` the same way. Their compatibility with the inclusions of the valuation
rings in their fraction fields is the square of site morphisms underlying the filler of `q₂`,
which exists because two 2-isomorphic 1-morphisms of represented categories fibred in groupoids
have the *same* underlying morphism of the site
(`AlgebraicGeometry.Stack.schemeMapOfFunctor_eq_of_basedNatTrans`).

**Locality of the ring map is the closed-point condition of Stacks 0CL2**, transported along the
identification of the points of a represented algebraic stack with the points of its scheme. That
identification has two descriptions in the library — through the chart of the representing
equivalence and through field-valued points — and
`AlgebraicGeometry.Stack.pointsHomeomorphScheme_eq_schemePoint` identifies them, after which the
closed point of `Spec q₂.R` is carried to the closed point of `Spec q.R` and
`IsLocalRing.isLocalHom_iff_comap_closedPoint` applies.

**The pasting identity is the interchange law twice, and it is proved over an arbitrary
bicategory.** The three 2-morphisms that build the dominating extension's commuting square and the
dotted arrow's two 2-cells appear in the order `τ, γ₂, τ', ι` on one side of the Stacks 0H18
compatibility triangle and in the order `τ, ι, γ₂, τ'` on the other, so the identity is two
applications of `CategoryTheory.Bicategory.whisker_exchange` with bicategorical coherence in
between. Stated over an arbitrary bicategory with every associator written out — which is
`CategoryTheory.Bicategory.pastingCompatOfExchange` — the coherence steps are discharged by the
`bicategory` tactic; stated over the 2-category of categories fibred in groupoids it would not be,
because the composites involved are type-correct only at default transparency and `rw` works at
`implicit` transparency.

The remaining ingredient is that the filler of a valuative square is the filler of the canonical
base change whiskered by the generic section
(`AlgebraicGeometry.Stack.ValuativeSquare.gamma_eq_whiskerLeft_baseChangeIso`), and it holds
**by `rfl`**: the generic section is the *strict* comparison
`AlgebraicGeometry.Stack.canonicalPreHomAlgebraicStacks`, whose two comparison 2-cells are
identities, so the Stacks 003O compatibility square it satisfies is definitional. Deriving it from
that square instead is unnecessary.

The dominating extension is assembled through
`AlgebraicGeometry.Stack.ValuativeSquare.exists_of_rebase`, which generalises the base morphism of
the extension and substitutes it, so that no field of the extension needs an `eqToHom`.

## References

* [Stacks Project, Tag 003O](https://stacks.math.columbia.edu/tag/003O)
* [Stacks Project, Tag 004B](https://stacks.math.columbia.edu/tag/004B)
* [Stacks Project, Tag 0CL2](https://stacks.math.columbia.edu/tag/0CL2)
* [Stacks Project, Tag 0CLK](https://stacks.math.columbia.edu/tag/0CLK)
* [Stacks Project, Tag 0CLX](https://stacks.math.columbia.edu/tag/0CLX)
* [Stacks Project, Tag 0H18](https://stacks.math.columbia.edu/tag/0H18)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Bicategory

namespace CategoryTheory.Bicategory

universe w' v' u'

/-- **The interchange law twice.** Two pastings of one diagram of four 2-morphisms agree: on the
left the 2-morphisms `ta`, `g2`, `tk`, `io` are composed in that order and on the right in the
order `ta`, `io`, `g2`, `tk`, and the two orders are reconciled by moving `io` past `tk` and then
past `g2`.

This is the Stacks 0H18 compatibility triangle for the dotted arrow of Stacks 0CLX, with every
associator written out so that the statement makes sense over an arbitrary bicategory. -/
theorem pastingCompatOfExchange {Bc : Type u'} [Bicategory.{w', v'} Bc]
    {s t G P Aa Xx Yy : Bc}
    (j : s ⟶ t) (Y2 : t ⟶ P) (X2 : s ⟶ G) (gs : G ⟶ P)
    (fs : P ⟶ Aa) (sn : P ⟶ Xx) (qy : Aa ⟶ Yy) (fh : Xx ⟶ Yy)
    (AA : t ⟶ Aa) (KK : s ⟶ G)
    (ta : AA ⟶ Y2 ≫ fs) (tk : X2 ⟶ KK)
    (g2 : j ≫ Y2 ⟶ X2 ≫ gs) (io : fs ≫ qy ⟶ sn ≫ fh)
    (qg : ((gs ≫ fs) ≫ qy) ⟶ ((gs ≫ sn) ≫ fh))
    (hqg : qg = (α_ gs fs qy).hom ≫ (gs ◁ io) ≫ (α_ gs sn fh).inv) :
    (α_ j AA qy).inv ≫
      (((j ◁ ta) ≫ (α_ j Y2 fs).inv ≫ (g2 ▷ fs) ≫ (α_ X2 gs fs).hom ≫
          (tk ▷ (gs ≫ fs))) ▷ qy) ≫
      (α_ KK (gs ≫ fs) qy).hom ≫ (KK ◁ qg) ≫ (α_ KK (gs ≫ sn) fh).inv
    = (j ◁ ((ta ▷ qy) ≫ (α_ Y2 fs qy).hom ≫ (Y2 ◁ io) ≫ (α_ Y2 sn fh).inv)) ≫
      (α_ j (Y2 ≫ sn) fh).inv ≫
      (((α_ j Y2 sn).inv ≫ (g2 ▷ sn) ≫ (α_ X2 gs sn).hom ≫ (tk ▷ (gs ≫ sn))) ▷ fh) := by
  subst hqg
  calc (α_ j AA qy).inv ≫
        (((j ◁ ta) ≫ (α_ j Y2 fs).inv ≫ (g2 ▷ fs) ≫ (α_ X2 gs fs).hom ≫
            (tk ▷ (gs ≫ fs))) ▷ qy) ≫
        (α_ KK (gs ≫ fs) qy).hom ≫
        (KK ◁ ((α_ gs fs qy).hom ≫ (gs ◁ io) ≫ (α_ gs sn fh).inv)) ≫
        (α_ KK (gs ≫ sn) fh).inv
      = (j ◁ (ta ▷ qy)) ≫ (j ◁ (α_ Y2 fs qy).hom) ≫
          (α_ j Y2 (fs ≫ qy)).inv ≫ (g2 ▷ (fs ≫ qy)) ≫
          (α_ X2 gs (fs ≫ qy)).hom ≫ (tk ▷ (gs ≫ fs ≫ qy)) ≫
          (KK ◁ (gs ◁ io)) ≫ (KK ◁ (α_ gs sn fh).inv) ≫
          (α_ KK (gs ≫ sn) fh).inv := by bicategory
    _ = (j ◁ (ta ▷ qy)) ≫ (j ◁ (α_ Y2 fs qy).hom) ≫
          (α_ j Y2 (fs ≫ qy)).inv ≫ (g2 ▷ (fs ≫ qy)) ≫
          (α_ X2 gs (fs ≫ qy)).hom ≫ (X2 ◁ (gs ◁ io)) ≫ (tk ▷ (gs ≫ sn ≫ fh)) ≫
          (KK ◁ (α_ gs sn fh).inv) ≫ (α_ KK (gs ≫ sn) fh).inv := by
        rw [← reassoc_of% whisker_exchange tk (gs ◁ io)]
    _ = (j ◁ (ta ▷ qy)) ≫ (j ◁ (α_ Y2 fs qy).hom) ≫
          (α_ j Y2 (fs ≫ qy)).inv ≫ (g2 ▷ (fs ≫ qy)) ≫ ((X2 ≫ gs) ◁ io) ≫
          (α_ X2 gs (sn ≫ fh)).hom ≫ (tk ▷ (gs ≫ sn ≫ fh)) ≫
          (KK ◁ (α_ gs sn fh).inv) ≫ (α_ KK (gs ≫ sn) fh).inv := by bicategory
    _ = (j ◁ (ta ▷ qy)) ≫ (j ◁ (α_ Y2 fs qy).hom) ≫
          (α_ j Y2 (fs ≫ qy)).inv ≫ ((j ≫ Y2) ◁ io) ≫ (g2 ▷ (sn ≫ fh)) ≫
          (α_ X2 gs (sn ≫ fh)).hom ≫ (tk ▷ (gs ≫ sn ≫ fh)) ≫
          (KK ◁ (α_ gs sn fh).inv) ≫ (α_ KK (gs ≫ sn) fh).inv := by
        rw [← reassoc_of% whisker_exchange g2 io]
    _ = (j ◁ ((ta ▷ qy) ≫ (α_ Y2 fs qy).hom ≫ (Y2 ◁ io) ≫ (α_ Y2 sn fh).inv)) ≫
          (α_ j (Y2 ≫ sn) fh).inv ≫
          (((α_ j Y2 sn).inv ≫ (g2 ▷ sn) ≫ (α_ X2 gs sn).hom ≫
            (tk ▷ (gs ≫ sn))) ▷ fh) := by bicategory

end CategoryTheory.Bicategory

namespace AlgebraicGeometry.Stack

universe u w

/-! ### 2-Yoneda for represented categories fibred in groupoids -/

/-- A transport cancels against its inverse around an identity.

The statement is about an abstract category because the goal it is applied to mentions the object
part of a `CategoryTheory.BasedCategory.ofFunctor`, which is semireducible, and is therefore not
type-correct at `implicit` transparency; stated here with opaque morphisms the step is an ordinary
`simp`. -/
theorem eqToHom_id_fac {C : Type*} [Category C] {A W' Gb T : C}
    (hF : W' = A) (h1 : A = W') (h2 : W' = Gb) (g : Gb ⟶ T) :
    eqToHom hF ≫ (eqToHom h1 ≫ 𝟙 W' ≫ eqToHom h2) ≫ g = eqToHom h2 ≫ g := by
  cases h1
  cases h2
  simp

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Two 2-isomorphic 1-morphisms of represented categories fibred in groupoids have the same
underlying morphism of the site.** The component of the 2-morphism at the terminal object of the
source slice lies over an identity, so it does not move the structure morphism; this is the
converse of `AlgebraicGeometry.Stack.basedNatTransOfSchemeMapEq`. -/
theorem schemeMapOfFunctor_eq_of_basedNatTrans {W U : BigFppfOver B S hS}
    {F G : (schemeFibredCategory B S hS W).based ⥤ᵇ (schemeFibredCategory B S hS U).based}
    (η : BasedNatTrans F G) :
    schemeMapOfFunctor B S hS F = schemeMapOfFunctor B S hS G := by
  have inst : (Over.forget U).IsHomLift (𝟙 W) (η.toNatTrans.app (Over.mk (𝟙 W))) :=
    η.isHomLift' (Over.mk (𝟙 W))
  have hw := Over.w (η.toNatTrans.app (Over.mk (𝟙 W)))
  have hfac : (η.toNatTrans.app (Over.mk (𝟙 W))).left
      = eqToHom (F.w_obj (Over.mk (𝟙 W))) ≫ 𝟙 W ≫ eqToHom (G.w_obj (Over.mk (𝟙 W))).symm :=
    IsHomLift.fac' (Over.forget U) (𝟙 W) (η.toNatTrans.app (Over.mk (𝟙 W)))
  change eqToHom (F.w_obj (Over.mk (𝟙 W))).symm ≫ (F.obj (Over.mk (𝟙 W))).hom = _
  refine Eq.trans (congrArg
    (fun k => eqToHom (F.w_obj (Over.mk (𝟙 W))).symm ≫ k) hw.symm) ?_
  refine Eq.trans (congrArg
    (fun k => eqToHom (F.w_obj (Over.mk (𝟙 W))).symm ≫ k ≫ (G.obj (Over.mk (𝟙 W))).hom)
    hfac) ?_
  change _ = eqToHom (G.w_obj (Over.mk (𝟙 W))).symm ≫ (G.obj (Over.mk (𝟙 W))).hom
  exact eqToHom_id_fac _ _ _ _

/-- The morphism of the site underlying a 1-morphism *postcomposed* with the one induced by a
morphism of the site; the companion of
`AlgebraicGeometry.Stack.schemeMapOfFunctor_comp_overMapBased`. -/
theorem schemeMapOfFunctor_comp_overMapBased' {Q W U : BigFppfOver B S hS}
    (b : (schemeFibredCategory B S hS Q).based ⥤ᵇ (schemeFibredCategory B S hS W).based)
    (g : W ⟶ U) :
    schemeMapOfFunctor B S hS (BasedFunctor.comp b (overMapBased B S hS g)) =
      schemeMapOfFunctor B S hS b ≫ g :=
  (Category.assoc _ _ _).symm

/-- A morphism of site objects is compatible with their structure morphisms to `S`. -/
theorem base_comp_of_siteHom {T T' : Scheme.{u}} (hT : B.Contains T) (hT' : B.Contains T')
    (b : T ⟶ S) (b' : T' ⟶ S) (g : siteObject B S hS hT b ⟶ siteObject B S hS hT' b') :
    (BigFppfOver.toScheme B S hS).map g ≫ b' = b := by
  refine Eq.trans ?_ (congrArg B.inclusion.map (Over.w g))
  exact (B.inclusion.map_comp g.left (siteObject B S hS hT' b').hom).symm

/-! ### The two descriptions of the points of a represented algebraic stack -/

attribute [local instance] Stack.pointTopology

/-- **The two models of the points of a represented algebraic stack agree.** The homeomorphism
`AlgebraicGeometry.Stack.pointsHomeomorphScheme`, built from the chart of the representing
equivalence, is the map `AlgebraicGeometry.Stack.schemePoint` read off field-valued points. -/
theorem pointsHomeomorphScheme_eq_schemePoint (U : BigFppfOver B S hS)
    (zz : points B S hS (schemeFibredCategory B S hS U).val
      (schemeFibredCategory B S hS U).property) :
    pointsHomeomorphScheme B S hS U zz = schemePoint B S hS U zz := by
  obtain ⟨x, rfl⟩ := (bijective_representedChartPointMap B S hS U).2 zz
  rw [pointsHomeomorphScheme_representedChartPointMap]
  symm
  induction x using Quot.inductionOn with
  | h p =>
    unfold representedChartPointMap
    rw [spacePointMap_class]
    rfl

/-- The closed point of a represented spectrum, read as a point of the category fibred in
groupoids it represents, has the closed point as its underlying scheme point. -/
theorem schemePoint_closedPointFieldValuedPoint (U : BigFppfOver B S hS) (z : U.left.1)
    (hz : B.Contains (Spec (.of (U.left.1.residueField z)))) :
    schemePoint B S hS U (pointClass B S hS (schemeFibredCategory B S hS U).val
      (schemeFibredCategory B S hS U).property
      (closedPointFieldValuedPoint B S hS U z hz)) = z :=
  ((BigFppfOver.toScheme B S hS).obj U).fromSpecResidueField_apply z _

/-! ### The Stacks 003O compatibility of the generic section -/

variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} {f : 𝒳 ⟶ 𝒴}

namespace ValuativeSquare

open CatFiberedInGroupoids

/-- **The filler of a valuative square is the filler of the canonical base change whiskered by
the generic section.** The generic section is the *strict* comparison of the solid square with the
canonical base change, so both comparison 2-cells of
`AlgebraicGeometry.Stack.canonicalPreHomAlgebraicStacks` are identities and the Stacks 003O
compatibility square says exactly this. -/
theorem gamma_eq_whiskerLeft_baseChangeIso (q : ValuativeSquare B S hS f) :
    q.γ = (genericSection.{u, w} B S hS q).hom ◁
      ((baseChangeSquare.{u, w} B S hS q).iso.hom.hom) := rfl

/-! ### The data a valuative square for the generic section supplies -/

variable (q : ValuativeSquare B S hS f)
  (q₂ : ValuativeSquare B S hS (genericSection.{u, w} B S hS q))

/-- The morphism of the site underlying the special point of a valuative square for the generic
section, followed by the projection to `Spec A`. -/
noncomputable abbrev specialOverOfGenericSection :
    siteObject B S hS q₂.ring_mem q₂.base ⟶ siteObject B S hS q.ring_mem q.base :=
  schemeMapOfFunctor B S hS (q₂.y ≫ (baseChangeSquare.{u, w} B S hS q).fst.hom).hom

/-- The morphism of the site underlying the generic point of a valuative square for the generic
section. -/
noncomputable abbrev genericOverOfGenericSection :
    siteObject B S hS q₂.field_mem
      (Spec.map (CommRingCat.ofHom (algebraMap q₂.R q₂.K)) ≫ q₂.base) ⟶
    siteObject B S hS q.field_mem
      (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base) :=
  schemeMapOfFunctor B S hS q₂.x.hom

/-- **The dominating ring map of Stacks 0CLX.** `Spec` is fully faithful, so the morphism of
spectra underlying `specialOverOfGenericSection` is `Spec` of a ring map `q.R →+* q₂.R`. -/
noncomputable abbrev ringMapOfGenericSection : q.R →+* q₂.R :=
  (Spec.preimage ((BigFppfOver.toScheme B S hS).map
    (specialOverOfGenericSection.{u, w} B S hS q q₂))).hom

/-- **The field extension of Stacks 0CLX**, obtained from
`genericOverOfGenericSection` the same way. -/
noncomputable abbrev fieldMapOfGenericSection : q.K →+* q₂.K :=
  (Spec.preimage ((BigFppfOver.toScheme B S hS).map
    (genericOverOfGenericSection.{u, w} B S hS q q₂))).hom

/-- `Spec` of the dominating ring map is the morphism of spectra it came from. -/
private theorem spec_map_ringMapOfGenericSection :
    Spec.map (CommRingCat.ofHom (ringMapOfGenericSection.{u, w} B S hS q q₂))
      = (BigFppfOver.toScheme B S hS).map (specialOverOfGenericSection.{u, w} B S hS q q₂) :=
  Spec.map_preimage _

/-- `Spec` of the field extension is the morphism of spectra it came from. -/
private theorem spec_map_fieldMapOfGenericSection :
    Spec.map (CommRingCat.ofHom (fieldMapOfGenericSection.{u, w} B S hS q q₂))
      = (BigFppfOver.toScheme B S hS).map (genericOverOfGenericSection.{u, w} B S hS q q₂) :=
  Spec.map_preimage _

/-- The square of site morphisms underlying the filler of a valuative square for the generic
section: the filler is a 2-morphism between two 1-morphisms of represented categories fibred in
groupoids, and 2-isomorphic such 1-morphisms have the same underlying morphism of the site. -/
theorem genericMap_comp_specialOverOfGenericSection :
    q₂.genericMap ≫ specialOverOfGenericSection.{u, w} B S hS q q₂
      = genericOverOfGenericSection.{u, w} B S hS q q₂ ≫ q.genericMap := by
  have hj₂ : q₂.j.hom = overMapBased B S hS q₂.genericMap :=
    BasedFunctor.eq_of_toFunctor_eq q₂.j_canonical
  have hj : q.j.hom = overMapBased B S hS q.genericMap :=
    BasedFunctor.eq_of_toFunctor_eq q.j_canonical
  have h1 : schemeMapOfFunctor B S hS
      (q₂.j ≫ (q₂.y ≫ (baseChangeSquare.{u, w} B S hS q).fst.hom)).hom
      = q₂.genericMap ≫ specialOverOfGenericSection.{u, w} B S hS q q₂ := by
    rw [show (q₂.j ≫ (q₂.y ≫ (baseChangeSquare.{u, w} B S hS q).fst.hom)).hom
        = BasedFunctor.comp (overMapBased B S hS q₂.genericMap)
          (q₂.y ≫ (baseChangeSquare.{u, w} B S hS q).fst.hom).hom from by rw [← hj₂]; rfl]
    exact schemeMapOfFunctor_comp_overMapBased B S hS _ _
  have h2 : schemeMapOfFunctor B S hS (q₂.x ≫ q.j).hom
      = genericOverOfGenericSection.{u, w} B S hS q q₂ ≫ q.genericMap := by
    rw [show (q₂.x ≫ q.j).hom
        = BasedFunctor.comp q₂.x.hom (overMapBased B S hS q.genericMap) from by rw [← hj]; rfl]
    exact schemeMapOfFunctor_comp_overMapBased' B S hS _ _
  exact h1.symm.trans ((schemeMapOfFunctor_eq_of_basedNatTrans B S hS
    (q₂.γ ▷ (baseChangeSquare.{u, w} B S hS q).fst.hom).hom).trans h2)

/-- The two ring maps of Stacks 0CLX are compatible with the inclusions of the valuation rings in
their fraction fields. -/
theorem fraction_comm_ofGenericSection :
    (algebraMap q₂.R q₂.K).comp (ringMapOfGenericSection.{u, w} B S hS q q₂)
      = (fieldMapOfGenericSection.{u, w} B S hS q q₂).comp (algebraMap q.R q.K) := by
  have hspec : Spec.map (CommRingCat.ofHom (algebraMap q₂.R q₂.K)) ≫
        Spec.map (CommRingCat.ofHom (ringMapOfGenericSection.{u, w} B S hS q q₂))
      = Spec.map (CommRingCat.ofHom (fieldMapOfGenericSection.{u, w} B S hS q q₂)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) :=
    calc Spec.map (CommRingCat.ofHom (algebraMap q₂.R q₂.K)) ≫
          Spec.map (CommRingCat.ofHom (ringMapOfGenericSection.{u, w} B S hS q q₂))
        = B.inclusion.map q₂.genericMap.left ≫
            B.inclusion.map (specialOverOfGenericSection.{u, w} B S hS q q₂).left :=
          Eq.trans (congrArg (fun m => m ≫
              Spec.map (CommRingCat.ofHom (ringMapOfGenericSection.{u, w} B S hS q q₂)))
            q₂.genericMap_left.symm)
            (congrArg (fun m => B.inclusion.map q₂.genericMap.left ≫ m)
              (spec_map_ringMapOfGenericSection.{u, w} B S hS q q₂))
      _ = B.inclusion.map
            (q₂.genericMap ≫ specialOverOfGenericSection.{u, w} B S hS q q₂).left :=
          (B.inclusion.map_comp _ _).symm
      _ = B.inclusion.map
            (genericOverOfGenericSection.{u, w} B S hS q q₂ ≫ q.genericMap).left :=
          congrArg (fun m => B.inclusion.map (Over.Hom.left m))
            (genericMap_comp_specialOverOfGenericSection.{u, w} B S hS q q₂)
      _ = B.inclusion.map (genericOverOfGenericSection.{u, w} B S hS q q₂).left ≫
            B.inclusion.map q.genericMap.left := B.inclusion.map_comp _ _
      _ = Spec.map (CommRingCat.ofHom (fieldMapOfGenericSection.{u, w} B S hS q q₂)) ≫
            Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) :=
          Eq.trans (congrArg (fun m =>
              B.inclusion.map (genericOverOfGenericSection.{u, w} B S hS q q₂).left ≫ m)
            q.genericMap_left)
            (congrArg (fun m => m ≫ Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)))
              (spec_map_fieldMapOfGenericSection.{u, w} B S hS q q₂).symm)
  have hmap : CommRingCat.ofHom
        ((algebraMap q₂.R q₂.K).comp (ringMapOfGenericSection.{u, w} B S hS q q₂))
      = CommRingCat.ofHom
        ((fieldMapOfGenericSection.{u, w} B S hS q q₂).comp (algebraMap q.R q.K)) := by
    refine Spec.map_injective ?_
    rw [CommRingCat.ofHom_comp, CommRingCat.ofHom_comp, Spec.map_comp, Spec.map_comp]
    exact hspec
  exact congrArg CommRingCat.Hom.hom hmap

end ValuativeSquare

/-! ### Stacks 0CLX -/

open ValuativeSquare CatFiberedInGroupoids in
/-- **Stacks 0CLX.** A quasi-separated, universally closed 1-morphism of algebraic stacks
satisfies the existence part of the valuative criterion.

Given a valuative square `q`, the specialisation step
`AlgebraicGeometry.Stack.ValuativeSquare.exists_valuativeSquare_genericSection` produces a
valuative square `q₂` for the generic section of `q` whose closed point lies over the closed point
of `Spec q.R`. Its valuation ring and fraction field are the dominating extension; the two ring
maps come from 2-Yoneda and the full faithfulness of `Spec`; locality of the ring map is the
closed-point condition; and the dotted arrow is the special point of `q₂` followed by the
projection to `𝒳`. -/
@[stacks 0CLX]
theorem valuativeCriterionExistence_of_universallyClosed
    (hqs : AlgebraicStacks.IsQuasiSeparated B S hS f)
    (hclosed : AlgebraicStacks.UniversallyClosed B S hS f) :
    ValuativeCriterion.Existence B S hS f := by
  intro q
  obtain ⟨q₂, hz, hpt⟩ :=
    exists_valuativeSquare_genericSection.{u, w} B S hS q hqs hclosed
  -- the dominating valuation ring and the extension of the fraction field
  set rm := ringMapOfGenericSection.{u, w} B S hS q q₂ with hrm
  set fm := fieldMapOfGenericSection.{u, w} B S hS q q₂ with hfm
  set sOver := specialOverOfGenericSection.{u, w} B S hS q q₂ with hsOver
  set gOver := genericOverOfGenericSection.{u, w} B S hS q q₂ with hgOver
  have hringSpec := spec_map_ringMapOfGenericSection.{u, w} B S hS q q₂
  have hfieldSpec := spec_map_fieldMapOfGenericSection.{u, w} B S hS q q₂
  -- the ring map is local: it carries the closed point to the closed point
  have hclosedPt : (BigFppfOver.toScheme B S hS).map sOver
      (IsLocalRing.closedPoint q₂.R) = IsLocalRing.closedPoint q.R := by
    refine Eq.trans ?_ hpt
    refine Eq.trans ?_ (pointsHomeomorphScheme_eq_schemePoint B S hS _ _).symm
    refine Eq.symm ?_
    refine Eq.trans (congrArg (schemePoint B S hS (siteObject B S hS q.ring_mem q.base))
      (pointsMap_comp B S hS
        (schemeFibredCategory B S hS (siteObject B S hS q₂.ring_mem q₂.base)).val
        (schemeFibredCategory B S hS (siteObject B S hS q₂.ring_mem q₂.base)).property
        (baseChangeSquare.{u, w} B S hS q).pt.val.property
        (specialStack.{u, w} B S hS q).val.property
        q₂.y.hom (baseChangeSquare.{u, w} B S hS q).fst.hom.hom
        (pointClass B S hS
          (schemeFibredCategory B S hS (siteObject B S hS q₂.ring_mem q₂.base)).val
          (schemeFibredCategory B S hS (siteObject B S hS q₂.ring_mem q₂.base)).property
          (closedPointFieldValuedPoint B S hS (siteObject B S hS q₂.ring_mem q₂.base)
            (IsLocalRing.closedPoint q₂.R) hz)))) ?_
    refine Eq.trans (schemePoint_naturality B S hS
      (q₂.y ≫ (baseChangeSquare.{u, w} B S hS q).fst.hom).hom _) ?_
    exact congrArg (fun m => (BigFppfOver.toScheme B S hS).map sOver m)
      (schemePoint_closedPointFieldValuedPoint B S hS
        (siteObject B S hS q₂.ring_mem q₂.base) (IsLocalRing.closedPoint q₂.R) hz)
  have hlocal : IsLocalHom rm := by
    refine (IsLocalRing.isLocalHom_iff_comap_closedPoint rm).2 ?_
    refine Eq.trans ?_ hclosedPt
    exact Eq.trans (Spec.map_apply (CommRingCat.ofHom rm) (IsLocalRing.closedPoint q₂.R)).symm
      (congrArg (fun m => m (IsLocalRing.closedPoint q₂.R)) hringSpec)
  -- the comparison 2-morphisms between the induced 1-morphisms and the actual ones
  have hsMap : schemeMapOfFunctor B S hS (overMapBased B S hS sOver)
      = schemeMapOfFunctor B S hS
        (q₂.y ≫ (baseChangeSquare.{u, w} B S hS q).fst.hom).hom :=
    schemeMapOfFunctor_overMapBased B S hS sOver
  have hgMap : schemeMapOfFunctor B S hS q₂.x.hom
      = schemeMapOfFunctor B S hS (overMapBased B S hS gOver) :=
    (schemeMapOfFunctor_overMapBased B S hS gOver).symm
  have ta : schemeFibredCategoryMap B S hS sOver ⟶
      (q₂.y ≫ (baseChangeSquare.{u, w} B S hS q).fst.hom) :=
    Bicategory.InducedBicategory.mkHom₂ (basedNatTransOfSchemeMapEq B S hS _ _ hsMap)
  have tk : q₂.x ⟶ schemeFibredCategoryMap B S hS gOver :=
    Bicategory.InducedBicategory.mkHom₂ (basedNatTransOfSchemeMapEq B S hS _ _ hgMap)
  refine exists_of_rebase B S hS q q₂.R q₂.K rm fm hlocal
    (fraction_comm_ofGenericSection.{u, w} B S hS q q₂) q₂.ring_mem q₂.field_mem
    q₂.base ?_
    (Spec.map (CommRingCat.ofHom (algebraMap q₂.R q₂.K)) ≫ q₂.base) rfl
    sOver ?_ gOver ?_ q₂.genericMap q₂.genericMap_left
    q₂.j q₂.j_canonical
    (schemeFibredCategoryMap B S hS sOver) rfl
    (schemeFibredCategoryMap B S hS gOver) rfl
    ((q₂.j ◁ ta) ≫
      (α_ q₂.j q₂.y (baseChangeSquare.{u, w} B S hS q).fst.hom).inv ≫
      (q₂.γ ▷ (baseChangeSquare.{u, w} B S hS q).fst.hom) ≫
      (α_ q₂.x (genericSection.{u, w} B S hS q).hom
        (baseChangeSquare.{u, w} B S hS q).fst.hom).hom ≫
      (tk ▷ ((genericSection.{u, w} B S hS q).hom ≫
        (baseChangeSquare.{u, w} B S hS q).fst.hom)))
    ⟨?_⟩
  · exact Eq.trans (congrArg (fun m => m ≫ q.base) hringSpec)
      (base_comp_of_siteHom B S hS q₂.ring_mem q.ring_mem q₂.base q.base sOver)
  · exact hringSpec.symm
  · exact hfieldSpec.symm
  · exact
      { a := q₂.y ≫ (baseChangeSquare.{u, w} B S hS q).snd.hom
        α := (α_ q₂.j q₂.y (baseChangeSquare.{u, w} B S hS q).snd.hom).inv ≫
          (q₂.γ ▷ (baseChangeSquare.{u, w} B S hS q).snd.hom) ≫
          (α_ q₂.x (genericSection.{u, w} B S hS q).hom
            (baseChangeSquare.{u, w} B S hS q).snd.hom).hom ≫
          (tk ▷ ((genericSection.{u, w} B S hS q).hom ≫
            (baseChangeSquare.{u, w} B S hS q).snd.hom))
        β := (ta ▷ q.y) ≫
          (α_ q₂.y (baseChangeSquare.{u, w} B S hS q).fst.hom q.y).hom ≫
          (q₂.y ◁ (baseChangeSquare.{u, w} B S hS q).iso.hom.hom) ≫
          (α_ q₂.y (baseChangeSquare.{u, w} B S hS q).snd.hom f.hom).inv
        compat := Bicategory.pastingCompatOfExchange q₂.j q₂.y q₂.x
          (genericSection.{u, w} B S hS q).hom
          (baseChangeSquare.{u, w} B S hS q).fst.hom
          (baseChangeSquare.{u, w} B S hS q).snd.hom q.y f.hom
          (schemeFibredCategoryMap B S hS sOver)
          (schemeFibredCategoryMap B S hS gOver)
          ta tk q₂.γ ((baseChangeSquare.{u, w} B S hS q).iso.hom.hom) q.γ
          (Eq.trans (gamma_eq_whiskerLeft_baseChangeIso.{u, w} B S hS q)
            (Eq.trans
              (assocHom_comp (genericSection.{u, w} B S hS q).hom
                (baseChangeSquare.{u, w} B S hS q).fst.hom q.y
                (((genericSection.{u, w} B S hS q).hom ◁
                    (baseChangeSquare.{u, w} B S hS q).iso.hom.hom) ≫
                  (α_ (genericSection.{u, w} B S hS q).hom
                    (baseChangeSquare.{u, w} B S hS q).snd.hom f.hom).inv))
              (comp_assocInv (genericSection.{u, w} B S hS q).hom
                (baseChangeSquare.{u, w} B S hS q).snd.hom f.hom
                ((genericSection.{u, w} B S hS q).hom ◁
                  (baseChangeSquare.{u, w} B S hS q).iso.hom.hom))).symm) }

end AlgebraicGeometry.Stack

end
