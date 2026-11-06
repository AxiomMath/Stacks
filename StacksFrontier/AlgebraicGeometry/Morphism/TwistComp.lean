module

public import StacksFrontier.AlgebraicGeometry.Morphism.Composition
public import StacksFrontier.AlgebraicGeometry.Morphism.TwistExists

/-!
# Tag 07ZH, assertion (3): the maps on twists of a composite compose

**On the numbering.** Tag 07ZH's statement is unnumbered prose carrying three assertions — the two
displayed equations `U(ψ ∘ φ) = r_ψ^{-1}(U(φ))` and `r_{ψ ∘ φ} = r_φ ∘ r_ψ|_{U(ψ∘φ)}`, and then
`θ_ψ ∘ r_ψ^*θ_φ = θ_{ψ∘φ}`. "Assertion (1)/(2)/(3)" is this library's own labelling of those
three; **the numbers do not occur in the source.**

**On a typo in the source.** The source prints the first equation as
`U(ψ ∘ φ) = r_φ^{-1}(U(ψ))`, which is type-incorrect: `r_φ` is defined on `U(φ) ⊆ Proj_S(B)` and
`U(ψ) ⊆ Proj_S(C)`, so `r_φ^{-1}(U(ψ))` is not an open of anything. The intended statement, and
the one proved in `Morphism/Composition.lean` as
`Stacks.AlgebraicGeometry.RelativeProjMapComp.relativeMapDomain_comp`, has `φ` and `ψ`
interchanged: `U(ψ ∘ φ) = r_ψ^{-1}(U(φ))`, an open of `Proj_S(C)`.

Let `φ : A ⟶ B` and `ψ : B ⟶ C` be homomorphisms of quasi-coherent graded `𝒪_S`-algebras. Tag 07ZG
attaches to each of them an open of the relative Proj of its target, a morphism out of that open,
and for every `n : ℤ` a map on the `n`-th twists. Tag 07ZH's third assertion compares the three
maps on twists.

## References

* [Stacks Project, Tag 07ZH](https://stacks.math.columbia.edu/tag/07ZH)
* [Stacks Project, Tag 07ZG](https://stacks.math.columbia.edu/tag/07ZG)
* [Stacks Project, Tag 01MZ](https://stacks.math.columbia.edu/tag/01MZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjShared
open Stacks.AlgebraicGeometry.ProjTwistChain
open Stacks.AlgebraicGeometry.ProjTwistCompare
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjMapDomain
open Stacks.AlgebraicGeometry.Tag07ZGMorphism

namespace Stacks.AlgebraicGeometry.Tag07ZGTwist

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj
attribute [local instance_reducible] ProjectiveSpectrum.top

universe u

/-! ### Transport of a morphism between inverse images to a precomposed leg -/

section Generic

variable {X Y Y' V Z Z' : Scheme.{u}}

/-- **The transport of a morphism between two inverse images to a precomposed pair of legs.** A
morphism `α` between the inverse images of `M` along `a` and of `N` along `b` is carried, by the
pseudofunctoriality identifications of the inverse image, to a morphism between the inverse images
along `w ≫ a` and `w ≫ b`; the two composites are named by the equations `hd` and `hi`, so that
neither `a` nor `b` occurs in the type. -/
public def legTransport (w : Z ⟶ V) {a : V ⟶ X} {b : V ⟶ Y} {M : X.Modules} {N : Y.Modules}
    (α : (Scheme.Modules.pullback a).obj M ⟶ (Scheme.Modules.pullback b).obj N)
    {d : Z ⟶ X} (hd : w ≫ a = d) {i : Z ⟶ Y} (hi : w ≫ b = i) :
    (Scheme.Modules.pullback d).obj M ⟶ (Scheme.Modules.pullback i).obj N :=
  (Scheme.Modules.pullbackCongr hd).inv.app M ≫
    (Scheme.Modules.pullbackComp w a).inv.app M ≫
    (Scheme.Modules.pullback w).map α ≫
    (Scheme.Modules.pullbackComp w b).hom.app N ≫
    (Scheme.Modules.pullbackCongr hi).hom.app N

/-- The transport to a precomposed leg, as the composite of its five factors. -/
public theorem legTransport_def (w : Z ⟶ V) {a : V ⟶ X} {b : V ⟶ Y} {M : X.Modules}
    {N : Y.Modules}
    (α : (Scheme.Modules.pullback a).obj M ⟶ (Scheme.Modules.pullback b).obj N)
    {d : Z ⟶ X} (hd : w ≫ a = d) {i : Z ⟶ Y} (hi : w ≫ b = i) :
    legTransport w α hd hi =
      (Scheme.Modules.pullbackCongr hd).inv.app M ≫
        (Scheme.Modules.pullbackComp w a).inv.app M ≫
        (Scheme.Modules.pullback w).map α ≫
        (Scheme.Modules.pullbackComp w b).hom.app N ≫
        (Scheme.Modules.pullbackCongr hi).hom.app N :=
  rfl

/-- **The transport to a precomposed leg is compatible with composition.** The two transports of a
composable pair, taken at a common middle leg, compose to the transport of the composite. -/
public theorem legTransport_comp (w : Z ⟶ V) {a : V ⟶ X} {b : V ⟶ Y} {c : V ⟶ Y'}
    {M : X.Modules} {N : Y.Modules} {P : Y'.Modules}
    (α : (Scheme.Modules.pullback a).obj M ⟶ (Scheme.Modules.pullback b).obj N)
    (β : (Scheme.Modules.pullback b).obj N ⟶ (Scheme.Modules.pullback c).obj P)
    {d : Z ⟶ X} (hd : w ≫ a = d) {m : Z ⟶ Y} (hm : w ≫ b = m) {i : Z ⟶ Y'}
    (hi : w ≫ c = i) :
    legTransport w α hd hm ≫ legTransport w β hm hi = legTransport w (α ≫ β) hd hi := by
  simp only [legTransport_def, Category.assoc, Functor.map_comp]
  rw [Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app_assoc]

/-- The transport to a precomposed leg of two equal morphisms agree. -/
public theorem legTransport_congr (w : Z ⟶ V) {a : V ⟶ X} {b : V ⟶ Y} {M : X.Modules}
    {N : Y.Modules}
    {α β : (Scheme.Modules.pullback a).obj M ⟶ (Scheme.Modules.pullback b).obj N}
    (h : α = β) {d : Z ⟶ X} (hd : w ≫ a = d) {i : Z ⟶ Y} (hi : w ≫ b = i) :
    legTransport w α hd hi = legTransport w β hd hi := by
  rw [h]

/-- **The transport to a precomposed leg is faithful**: the inverse image along the leg is
recovered from it, the four outer factors being isomorphisms. -/
public theorem pullback_map_eq_of_legTransport_eq (w : Z ⟶ V) {a : V ⟶ X} {b : V ⟶ Y}
    {M : X.Modules} {N : Y.Modules}
    {α β : (Scheme.Modules.pullback a).obj M ⟶ (Scheme.Modules.pullback b).obj N}
    {d : Z ⟶ X} (hd : w ≫ a = d) {i : Z ⟶ Y} (hi : w ≫ b = i)
    (h : legTransport w α hd hi = legTransport w β hd hi) :
    (Scheme.Modules.pullback w).map α = (Scheme.Modules.pullback w).map β := by
  rw [legTransport_def, legTransport_def] at h
  replace h := (Iso.cancel_iso_inv_left ((Scheme.Modules.pullbackCongr hd).app M) _ _).mp h
  replace h := (Iso.cancel_iso_inv_left ((Scheme.Modules.pullbackComp w a).app M) _ _).mp h
  exact (Iso.cancel_iso_hom_right _ _ ((Scheme.Modules.pullbackComp w b).app N ≪≫
    (Scheme.Modules.pullbackCongr hi).app N)).mp h

/-- **The transport to a leg which is itself a composite.** Transporting to `w ≫ q` is
transporting to `q` and then to `w`; this is
`Stacks.AlgebraicGeometry.Tag07ZGTwist.pullback_five_comp_leg` in the vocabulary of
`legTransport`. -/
public theorem legTransport_legTransport (w : Z' ⟶ Z) (q : Z ⟶ V) {a : V ⟶ X} {b : V ⟶ Y}
    {M : X.Modules} {N : Y.Modules}
    (α : (Scheme.Modules.pullback a).obj M ⟶ (Scheme.Modules.pullback b).obj N)
    {d : Z ⟶ X} (hd : q ≫ a = d) {i : Z ⟶ Y} (hi : q ≫ b = i)
    {d' : Z' ⟶ X} (hd' : (w ≫ q) ≫ a = d') (hwd : w ≫ d = d')
    {i' : Z' ⟶ Y} (hi' : (w ≫ q) ≫ b = i') (hwi : w ≫ i = i') :
    legTransport (w ≫ q) α hd' hi' = legTransport w (legTransport q α hd hi) hwd hwi :=
  pullback_five_comp_leg w q a b α hd hi hd' hwd hi' hwi

/-- The congruence isomorphism of the inverse image at a reflexive equation is the identity
(`inv` direction). -/
private theorem pullbackCongr_inv_app_self (f : Z ⟶ X) (hf : f = f) (M : X.Modules) :
    (Scheme.Modules.pullbackCongr hf).inv.app M = 𝟙 _ := by
  rw [pullbackCongr_refl_eq]
  rfl

/-- The congruence isomorphism of the inverse image at a reflexive equation is the identity
(`hom` direction). -/
private theorem pullbackCongr_hom_app_self (f : Z ⟶ X) (hf : f = f) (M : X.Modules) :
    (Scheme.Modules.pullbackCongr hf).hom.app M = 𝟙 _ := by
  rw [pullbackCongr_refl_eq]
  rfl

end Generic

/-! ### The chart identification of the relative twists, read at a leg -/

variable {S : Scheme.{u}} {A B C : SheafGradedAlgebra S}

/-- **Tag 01NR's chart identification of the `n`-th relative twist, read at a leg.** A morphism `g`
from a scheme `Z` to `Proj Γ(U, A)` presents the inverse image along `g ≫ i_U` of the `n`-th
relative twist; this is the chart identification transported to it, with the composite named by the
equation `hc` so that the chart does not occur in the type. -/
public def chartTwistAt (A : SheafGradedAlgebra S) (n : ℤ) (U : S.affineOpens) {Z : Scheme.{u}}
    (g : Z ⟶ AlgebraicGeometry.Proj (A.grading U.1))
    {c : Z ⟶ (relativeProj A).scheme} (hc : g ≫ (relativeProj A).chart U.1 U.2 = c) :
    (Scheme.Modules.pullback c).obj (relativeTwist A n) ⟶
      (Scheme.Modules.pullback g).obj (twistingSheaf (A.grading U.1) n) :=
  (Scheme.Modules.pullbackCongr hc).inv.app (relativeTwist A n) ≫
    (Scheme.Modules.pullbackComp g ((relativeProj A).chart U.1 U.2)).inv.app
      (relativeTwist A n) ≫
    (Scheme.Modules.pullback g).map (chartTwistIso A n U).hom

/-- The chart identification read at a leg, as the composite of its three factors. -/
public theorem chartTwistAt_def (A : SheafGradedAlgebra S) (n : ℤ) (U : S.affineOpens)
    {Z : Scheme.{u}} (g : Z ⟶ AlgebraicGeometry.Proj (A.grading U.1))
    {c : Z ⟶ (relativeProj A).scheme} (hc : g ≫ (relativeProj A).chart U.1 U.2 = c) :
    chartTwistAt A n U g hc =
      (Scheme.Modules.pullbackCongr hc).inv.app (relativeTwist A n) ≫
        (Scheme.Modules.pullbackComp g ((relativeProj A).chart U.1 U.2)).inv.app
          (relativeTwist A n) ≫
        (Scheme.Modules.pullback g).map (chartTwistIso A n U).hom :=
  rfl

/-- The chart identification read at a leg is an isomorphism: each of its three factors is. -/
public instance isIso_chartTwistAt (A : SheafGradedAlgebra S) (n : ℤ) (U : S.affineOpens)
    {Z : Scheme.{u}} (g : Z ⟶ AlgebraicGeometry.Proj (A.grading U.1))
    {c : Z ⟶ (relativeProj A).scheme} (hc : g ≫ (relativeProj A).chart U.1 U.2 = c) :
    IsIso (chartTwistAt A n U g hc) := by
  have h : chartTwistAt A n U g hc =
      (((Scheme.Modules.pullbackCongr hc).app (relativeTwist A n)).symm ≪≫
        ((Scheme.Modules.pullbackComp g ((relativeProj A).chart U.1 U.2)).app
            (relativeTwist A n)).symm ≪≫
        (Scheme.Modules.pullback g).mapIso (chartTwistIso A n U)).hom :=
    rfl
  rw [h]
  infer_instance

/-- **The chart identification read at a composed leg** is the chart identification read at the
second factor, transported to the first. This is
`Stacks.AlgebraicGeometry.Tag07ZGTwist.pullback_three_comp_leg` in the vocabulary of
`legTransport`. -/
public theorem chartTwistAt_leg (A : SheafGradedAlgebra S) (n : ℤ) (U : S.affineOpens)
    {Z Z' : Scheme.{u}} (k : Z' ⟶ Z) (g₀ : Z ⟶ AlgebraicGeometry.Proj (A.grading U.1))
    {c₀ : Z ⟶ (relativeProj A).scheme} (hc₀ : g₀ ≫ (relativeProj A).chart U.1 U.2 = c₀)
    {g : Z' ⟶ AlgebraicGeometry.Proj (A.grading U.1)} (hg : k ≫ g₀ = g)
    {c : Z' ⟶ (relativeProj A).scheme} (hc : g ≫ (relativeProj A).chart U.1 U.2 = c)
    (hkc : k ≫ c₀ = c) :
    chartTwistAt A n U g hc = legTransport k (chartTwistAt A n U g₀ hc₀) hkc hg := by
  subst hg
  refine Eq.trans (pullback_three_comp_leg k g₀ ((relativeProj A).chart U.1 U.2)
    (chartTwistIso A n U).hom hc₀ hc hkc) ?_
  refine Eq.trans ?_ (legTransport_def k (chartTwistAt A n U g₀ hc₀) hkc rfl).symm
  rw [pullbackCongr_hom_app_self (k ≫ g₀) rfl (twistingSheaf (A.grading U.1) n), Category.comp_id]
  rfl

/-- **Tag 01MY's comparison map read at a composed leg**, in the vocabulary of `legTransport`.
This is `Stacks.AlgebraicGeometry.Tag07ZGTwist.twistMapAt_comp_leg`. -/
public theorem twistMapAt_leg {R₁ R₂ : Type u} {σ : Type u} {τ : Type u} [CommRing R₁]
    [CommRing R₂] [SetLike σ R₁] [AddSubgroupClass σ R₁] [SetLike τ R₂] [AddSubgroupClass τ R₂]
    (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ] (φ : 𝒜 →+*ᵍ ℬ) (n : ℤ)
    {W' W : Scheme.{u}} (w : W' ⟶ W) (q : W ⟶ (mapDomain 𝒜 ℬ φ).toScheme)
    {d : W ⟶ AlgebraicGeometry.Proj 𝒜} (hd : q ≫ mapHom 𝒜 ℬ φ = d)
    {i : W ⟶ AlgebraicGeometry.Proj ℬ} (hi : q ≫ (mapDomain 𝒜 ℬ φ).ι = i)
    {d' : W' ⟶ AlgebraicGeometry.Proj 𝒜} (hd' : (w ≫ q) ≫ mapHom 𝒜 ℬ φ = d')
    (hwd : w ≫ d = d')
    {i' : W' ⟶ AlgebraicGeometry.Proj ℬ} (hi' : (w ≫ q) ≫ (mapDomain 𝒜 ℬ φ).ι = i')
    (hwi : w ≫ i = i') :
    twistMapAt 𝒜 ℬ φ n (w ≫ q) hd' hi' =
      legTransport w (twistMapAt 𝒜 ℬ φ n q hd hi) hwd hwi :=
  twistMapAt_comp_leg 𝒜 ℬ φ n w q hd hi hd' hwd hi' hwi

/-! ### The map on twists read at a leg through a piece -/

variable (ψ : SheafGradedAlgebraHom A B)

/-- **The map `θ_n` read at the inclusion of the piece over an affine open `U` of the base, against
the chart identifications.** Followed by the chart identification of the target, it is the chart
identification of the source followed by Tag 01MY's comparison map for `Γ(U, A) ⟶ Γ(U, B)`, read at
the identification of the piece with the absolute domain of definition.

This is `Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeTwistChart_comp_target` with the two
transported chart identifications named by `chartTwistAt` and the affine-local comparison map
traded for `θ_n` itself by `relativeTwistMap_chart`. -/
public theorem legTransport_relativeTwistMap_chart (n : ℤ) (U : S.affineOpens)
    {gd : (chartImage ψ U).toScheme ⟶ AlgebraicGeometry.Proj (A.grading U.1)}
    (hgd : (chartDomainIso ψ U).inv ≫
      mapHom (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1) = gd)
    (hcd : gd ≫ (relativeProj A).chart U.1 U.2 = pieceIncl ψ U ≫ relativeMapHom ψ)
    {gi : (chartImage ψ U).toScheme ⟶ AlgebraicGeometry.Proj (B.grading U.1)}
    (hgi : (chartDomainIso ψ U).inv ≫
      (mapDomain (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1)).ι = gi)
    (hci : gi ≫ (relativeProj B).chart U.1 U.2 = pieceIncl ψ U ≫ ψ.relativeMapDomain.ι) :
    legTransport (pieceIncl ψ U) (relativeTwistMap ψ n) rfl rfl ≫
        chartTwistAt B n U gi hci =
      chartTwistAt A n U gd hcd ≫
        twistMapAt (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1) n
          (chartDomainIso ψ U).inv hgd hgi := by
  subst hgd
  subst hgi
  rw [legTransport_def, pullbackCongr_inv_app_self, pullbackCongr_hom_app_self,
    relativeTwistMap_chart, chartTwistAt_def, chartTwistAt_def]
  simp only [Category.id_comp, Category.comp_id, Category.assoc]
  rw [relativeTwistChart_comp_target ψ n U hcd hci]
  simp only [Category.assoc]
  rw [Iso.inv_hom_id_app_assoc]

/-- **The map `θ_n` read at an arbitrary leg through the piece over an affine open `U` of the
base, against the chart identifications.** This is
`Stacks.AlgebraicGeometry.Tag07ZGTwist.legTransport_relativeTwistMap_chart` with every one of its
four maps read at a leg out of a further scheme, presented by a morphism `k` into the piece; all
six legs are arguments pinned by equations, so that neither the piece nor the absolute domain of
definition occurs in the type.

That is what lets the identity be applied at the three homomorphisms of a composable pair with the
three middle legs *literally* equal, which is what makes the comparison maps cancel. -/
public theorem legTransport_relativeTwistMap_chart_leg (n : ℤ) (U : S.affineOpens)
    {Z : Scheme.{u}} (k : Z ⟶ (chartImage ψ U).toScheme)
    {t : Z ⟶ ψ.relativeMapDomain.toScheme} (ht : k ≫ pieceIncl ψ U = t)
    {r : Z ⟶ (mapDomain (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1)).toScheme}
    (hr : k ≫ (chartDomainIso ψ U).inv = r)
    {d : Z ⟶ (relativeProj A).scheme} (hd : t ≫ relativeMapHom ψ = d)
    {i : Z ⟶ (relativeProj B).scheme} (hi : t ≫ ψ.relativeMapDomain.ι = i)
    {gd : Z ⟶ AlgebraicGeometry.Proj (A.grading U.1)}
    (hgd : r ≫ mapHom (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1) = gd)
    (hcd : gd ≫ (relativeProj A).chart U.1 U.2 = d)
    {gi : Z ⟶ AlgebraicGeometry.Proj (B.grading U.1)}
    (hgi : r ≫ (mapDomain (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1)).ι = gi)
    (hci : gi ≫ (relativeProj B).chart U.1 U.2 = i) :
    legTransport t (relativeTwistMap ψ n) hd hi ≫ chartTwistAt B n U gi hci =
      chartTwistAt A n U gd hcd ≫
        twistMapAt (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1) n r hgd hgi := by
  subst ht
  subst hr
  have hcd₀ : ((chartDomainIso ψ U).inv ≫
        mapHom (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1)) ≫
      (relativeProj A).chart U.1 U.2 = pieceIncl ψ U ≫ relativeMapHom ψ :=
    (Category.assoc _ _ _).trans (pieceIncl_comp_relativeMapHom ψ U).symm
  have hci₀ : ((chartDomainIso ψ U).inv ≫
        (mapDomain (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1)).ι) ≫
      (relativeProj B).chart U.1 U.2 = pieceIncl ψ U ≫ ψ.relativeMapDomain.ι :=
    (Category.assoc _ _ _).trans (pieceIncl_comp_ι ψ U).symm
  have hkd : k ≫ pieceIncl ψ U ≫ relativeMapHom ψ = d :=
    (Category.assoc _ _ _).symm.trans hd
  have hki : k ≫ pieceIncl ψ U ≫ ψ.relativeMapDomain.ι = i :=
    (Category.assoc _ _ _).symm.trans hi
  have hkgd : k ≫ (chartDomainIso ψ U).inv ≫
      mapHom (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1) = gd :=
    (Category.assoc _ _ _).symm.trans hgd
  have hkgi : k ≫ (chartDomainIso ψ U).inv ≫
      (mapDomain (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1)).ι = gi :=
    (Category.assoc _ _ _).symm.trans hgi
  rw [legTransport_legTransport k (pieceIncl ψ U) (relativeTwistMap ψ n) rfl rfl hd hkd hi hki,
    chartTwistAt_leg B n U k _ hci₀ hkgi hci hki,
    chartTwistAt_leg A n U k _ hcd₀ hkgd hcd hkd,
    twistMapAt_leg (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1) n k
      (chartDomainIso ψ U).inv rfl rfl hgd hkgd hgi hkgi]
  refine Eq.trans (legTransport_comp k _ _ hkd hki hkgi) ?_
  refine Eq.trans ?_ (legTransport_comp k _ _ hkd hkgd hkgi).symm
  exact legTransport_congr k
    (legTransport_relativeTwistMap_chart ψ n U rfl hcd₀ rfl hci₀) hkd hkgi

/-! ### Tag 01MZ's third assertion for a homomorphism equal to a composite -/

/-- **Stacks Tag 01MZ's third assertion at legs, for a homomorphism equal to a composite.** The
transport along the equality is a substitution, the homomorphism being a variable. -/
public theorem twistMapAt_comp_of_eq {R₁ R₂ R₃ : Type u} {σ : Type u} {τ : Type u} {υ : Type u}
    [CommRing R₁] [CommRing R₂] [CommRing R₃] [SetLike σ R₁] [AddSubgroupClass σ R₁]
    [SetLike τ R₂] [AddSubgroupClass τ R₂] [SetLike υ R₃] [AddSubgroupClass υ R₃]
    (𝒜 : ℕ → σ) (ℬ : ℕ → τ) (𝒞 : ℕ → υ) [GradedRing 𝒜] [GradedRing ℬ] [GradedRing 𝒞]
    (φ' : 𝒜 →+*ᵍ ℬ) (χ : ℬ →+*ᵍ 𝒞) {f : 𝒜 →+*ᵍ 𝒞} (hf : f = χ.comp φ') (n : ℤ)
    {W : Scheme.{u}} (q : W ⟶ (mapDomain 𝒜 𝒞 f).toScheme)
    (p : W ⟶ (mapDomain 𝒜 ℬ φ').toScheme) (j : W ⟶ (mapDomain ℬ 𝒞 χ).toScheme)
    {d : W ⟶ AlgebraicGeometry.Proj 𝒜} {m : W ⟶ AlgebraicGeometry.Proj ℬ}
    {i : W ⟶ AlgebraicGeometry.Proj 𝒞}
    (hqd : q ≫ mapHom 𝒜 𝒞 f = d) (hpd : p ≫ mapHom 𝒜 ℬ φ' = d)
    (hpm : p ≫ (mapDomain 𝒜 ℬ φ').ι = m) (hjm : j ≫ mapHom ℬ 𝒞 χ = m)
    (hqi : q ≫ (mapDomain 𝒜 𝒞 f).ι = i) (hji : j ≫ (mapDomain ℬ 𝒞 χ).ι = i) :
    twistMapAt 𝒜 𝒞 f n q hqd hqi =
      twistMapAt 𝒜 ℬ φ' n p hpd hpm ≫ twistMapAt ℬ 𝒞 χ n j hjm hji := by
  subst hf
  exact twistMapAt_comp 𝒜 ℬ 𝒞 φ' χ n q p j hqd hpd hpm hjm hqi hji

/-! ### The composition law on the pieces -/

section Comp

variable (φ : SheafGradedAlgebraHom A B) (ψ : SheafGradedAlgebraHom B C)

/-- **The composition law for the maps on twists, over the piece of `U(ψ ∘ φ)` over an affine open
`U` of the base, with the three absolute legs given.** The three maps on twists, read at the legs
out of the piece, satisfy the composition law because the absolute comparison maps of Tag 01MY for
`Γ(U, A) ⟶ Γ(U, B) ⟶ Γ(U, C)` do, by Tag 01MZ's third assertion, and because the chart
identification of the `n`-th relative twist of `Proj_S(B)` occurs once in each direction. -/
private theorem comp_chart_of (n : ℤ) (U : S.affineOpens)
    (a : (ψ.comp φ).relativeMapDomain.toScheme ⟶ φ.relativeMapDomain.toScheme)
    (b : (ψ.comp φ).relativeMapDomain.toScheme ⟶ ψ.relativeMapDomain.toScheme)
    (ha : a ≫ relativeMapHom φ = relativeMapHom (ψ.comp φ))
    {m : (ψ.comp φ).relativeMapDomain.toScheme ⟶ (relativeProj B).scheme}
    (hm₁ : a ≫ φ.relativeMapDomain.ι = m) (hm₂ : b ≫ relativeMapHom ψ = m)
    (hc : b ≫ ψ.relativeMapDomain.ι = (ψ.comp φ).relativeMapDomain.ι)
    (p : (chartImage (ψ.comp φ) U).toScheme ⟶
      (mapDomain (A.grading U.1) (B.grading U.1) (φ.sectionHom U.1)).toScheme)
    (j : (chartImage (ψ.comp φ) U).toScheme ⟶
      (mapDomain (B.grading U.1) (C.grading U.1) (ψ.sectionHom U.1)).toScheme)
    (kφ : (chartImage (ψ.comp φ) U).toScheme ⟶ (chartImage φ U).toScheme)
    (kψ : (chartImage (ψ.comp φ) U).toScheme ⟶ (chartImage ψ U).toScheme)
    (htφ : kφ ≫ pieceIncl φ U = pieceIncl (ψ.comp φ) U ≫ a)
    (hrφ : kφ ≫ (chartDomainIso φ U).inv = p)
    (htψ : kψ ≫ pieceIncl ψ U = pieceIncl (ψ.comp φ) U ≫ b)
    (hrψ : kψ ≫ (chartDomainIso ψ U).inv = j)
    {gd : (chartImage (ψ.comp φ) U).toScheme ⟶ AlgebraicGeometry.Proj (A.grading U.1)}
    (hgdA : (chartDomainIso (ψ.comp φ) U).inv ≫
      mapHom (A.grading U.1) (C.grading U.1) ((ψ.comp φ).sectionHom U.1) = gd)
    (hgdφ : p ≫ mapHom (A.grading U.1) (B.grading U.1) (φ.sectionHom U.1) = gd)
    (hcdA : gd ≫ (relativeProj A).chart U.1 U.2 =
      pieceIncl (ψ.comp φ) U ≫ relativeMapHom (ψ.comp φ))
    {gm : (chartImage (ψ.comp φ) U).toScheme ⟶ AlgebraicGeometry.Proj (B.grading U.1)}
    (hgmφ : p ≫ (mapDomain (A.grading U.1) (B.grading U.1) (φ.sectionHom U.1)).ι = gm)
    (hgmψ : j ≫ mapHom (B.grading U.1) (C.grading U.1) (ψ.sectionHom U.1) = gm)
    (hciB : gm ≫ (relativeProj B).chart U.1 U.2 = pieceIncl (ψ.comp φ) U ≫ m)
    {gi : (chartImage (ψ.comp φ) U).toScheme ⟶ AlgebraicGeometry.Proj (C.grading U.1)}
    (hgiA : (chartDomainIso (ψ.comp φ) U).inv ≫
      (mapDomain (A.grading U.1) (C.grading U.1) ((ψ.comp φ).sectionHom U.1)).ι = gi)
    (hgiψ : j ≫ (mapDomain (B.grading U.1) (C.grading U.1) (ψ.sectionHom U.1)).ι = gi)
    (hciC : gi ≫ (relativeProj C).chart U.1 U.2 =
      pieceIncl (ψ.comp φ) U ≫ (ψ.comp φ).relativeMapDomain.ι)
    (hf : (ψ.comp φ).sectionHom U.1 = (ψ.sectionHom U.1).comp (φ.sectionHom U.1)) :
    legTransport (pieceIncl (ψ.comp φ) U)
        (legTransport a (relativeTwistMap φ n) ha hm₁ ≫
          legTransport b (relativeTwistMap ψ n) hm₂ hc) rfl rfl =
      legTransport (pieceIncl (ψ.comp φ) U) (relativeTwistMap (ψ.comp φ) n) rfl rfl := by
  have h1 : (pieceIncl (ψ.comp φ) U ≫ a) ≫ relativeMapHom φ =
      pieceIncl (ψ.comp φ) U ≫ relativeMapHom (ψ.comp φ) := by rw [Category.assoc, ha]
  have h2 : (pieceIncl (ψ.comp φ) U ≫ a) ≫ φ.relativeMapDomain.ι =
      pieceIncl (ψ.comp φ) U ≫ m := by rw [Category.assoc, hm₁]
  have h3 : (pieceIncl (ψ.comp φ) U ≫ b) ≫ relativeMapHom ψ =
      pieceIncl (ψ.comp φ) U ≫ m := by rw [Category.assoc, hm₂]
  have h4 : (pieceIncl (ψ.comp φ) U ≫ b) ≫ ψ.relativeMapDomain.ι =
      pieceIncl (ψ.comp φ) U ≫ (ψ.comp φ).relativeMapDomain.ι := by rw [Category.assoc, hc]
  rw [(legTransport_comp (pieceIncl (ψ.comp φ) U)
      (legTransport a (relativeTwistMap φ n) ha hm₁)
      (legTransport b (relativeTwistMap ψ n) hm₂ hc) rfl rfl rfl).symm,
    (legTransport_legTransport (pieceIncl (ψ.comp φ) U) a (relativeTwistMap φ n) ha hm₁ h1 rfl
      h2 rfl).symm,
    (legTransport_legTransport (pieceIncl (ψ.comp φ) U) b (relativeTwistMap ψ n) hm₂ hc h3 rfl
      h4 rfl).symm,
    ← cancel_mono (chartTwistAt C n U gi hciC), Category.assoc,
    legTransport_relativeTwistMap_chart_leg ψ n U kψ htψ hrψ h3 h4 hgmψ hciB hgiψ hciC,
    ← Category.assoc,
    legTransport_relativeTwistMap_chart_leg φ n U kφ htφ hrφ h1 h2 hgdφ hcdA hgmφ hciB,
    Category.assoc,
    ← twistMapAt_comp_of_eq (A.grading U.1) (B.grading U.1) (C.grading U.1) (φ.sectionHom U.1)
      (ψ.sectionHom U.1) hf n (chartDomainIso (ψ.comp φ) U).inv p j hgdA hgdφ hgmφ hgmψ hgiA
      hgiψ,
    legTransport_relativeTwistMap_chart (ψ.comp φ) n U hgdA hcdA hgiA hciC]

/-- **The composition law for the maps on twists, over the piece of `U(ψ ∘ φ)` over an affine open
`U` of the base.** The three legs into the absolute domains of definition over `U` are built here
from Tag 01MZ's first two assertions for `Γ(U, A) ⟶ Γ(U, B) ⟶ Γ(U, C)`, read for the homomorphism
induced by the composite, which is only propositionally the composite of the two induced
homomorphisms. -/
private theorem comp_chart (n : ℤ) (U : S.affineOpens)
    (a : (ψ.comp φ).relativeMapDomain.toScheme ⟶ φ.relativeMapDomain.toScheme)
    (b : (ψ.comp φ).relativeMapDomain.toScheme ⟶ ψ.relativeMapDomain.toScheme)
    (ha : a ≫ relativeMapHom φ = relativeMapHom (ψ.comp φ))
    {m : (ψ.comp φ).relativeMapDomain.toScheme ⟶ (relativeProj B).scheme}
    (hm₁ : a ≫ φ.relativeMapDomain.ι = m) (hm₂ : b ≫ relativeMapHom ψ = m)
    (hc : b ≫ ψ.relativeMapDomain.ι = (ψ.comp φ).relativeMapDomain.ι) :
    legTransport (pieceIncl (ψ.comp φ) U)
        (legTransport a (relativeTwistMap φ n) ha hm₁ ≫
          legTransport b (relativeTwistMap ψ n) hm₂ hc) rfl rfl =
      legTransport (pieceIncl (ψ.comp φ) U) (relativeTwistMap (ψ.comp φ) n) rfl rfl := by
  have hf := SheafGradedAlgebraHom.sectionHom_comp ψ φ U.1
  have hle := RelativeProjMapComp.mapDomain_comp_le_of_eq (A.grading U.1) (B.grading U.1)
    (C.grading U.1) (φ.sectionHom U.1) (ψ.sectionHom U.1) hf
  obtain ⟨qa, hq1, hq2⟩ := RelativeProjMapComp.mapHom_comp_of_eq (A.grading U.1) (B.grading U.1)
    (C.grading U.1) (φ.sectionHom U.1) (ψ.sectionHom U.1) hf hle
  obtain ⟨p, hp⟩ : ∃ p, (chartDomainIso (ψ.comp φ) U).inv ≫ qa = p := ⟨_, rfl⟩
  obtain ⟨j, hj⟩ : ∃ j, (chartDomainIso (ψ.comp φ) U).inv ≫
      (AlgebraicGeometry.Proj (C.grading U.1)).homOfLE hle = j := ⟨_, rfl⟩
  have hrφ : (p ≫ (chartDomainIso φ U).hom) ≫ (chartDomainIso φ U).inv = p := by
    simp
  have hrψ : (j ≫ (chartDomainIso ψ U).hom) ≫ (chartDomainIso ψ U).inv = j := by
    simp
  have hgdφ : p ≫ mapHom (A.grading U.1) (B.grading U.1) (φ.sectionHom U.1) =
      (chartDomainIso (ψ.comp φ) U).inv ≫
        mapHom (A.grading U.1) (C.grading U.1) ((ψ.comp φ).sectionHom U.1) := by
    rw [← hp, Category.assoc, ← hq2]
  have hgmψ : j ≫ mapHom (B.grading U.1) (C.grading U.1) (ψ.sectionHom U.1) =
      p ≫ (mapDomain (A.grading U.1) (B.grading U.1) (φ.sectionHom U.1)).ι := by
    rw [← hj, ← hp, Category.assoc, Category.assoc, hq1]
  have hgiψ : j ≫ (mapDomain (B.grading U.1) (C.grading U.1) (ψ.sectionHom U.1)).ι =
      (chartDomainIso (ψ.comp φ) U).inv ≫
        (mapDomain (A.grading U.1) (C.grading U.1) ((ψ.comp φ).sectionHom U.1)).ι := by
    rw [← hj, Category.assoc, Scheme.homOfLE_ι]
  have htψ : (j ≫ (chartDomainIso ψ U).hom) ≫ pieceIncl ψ U =
      pieceIncl (ψ.comp φ) U ≫ b := by
    rw [← cancel_mono ψ.relativeMapDomain.ι]
    simp only [Category.assoc]
    rw [hc, pieceIncl_comp_ι ψ U, pieceIncl_comp_ι (ψ.comp φ) U, Iso.hom_inv_id_assoc,
      ← Category.assoc, hgiψ, Category.assoc]
  have hkey : (j ≫ (chartDomainIso ψ U).hom) ≫ pieceIncl ψ U ≫ relativeMapHom ψ =
      j ≫ mapHom (B.grading U.1) (C.grading U.1) (ψ.sectionHom U.1) ≫
        (relativeProj B).chart U.1 U.2 := by
    rw [pieceIncl_comp_relativeMapHom ψ U, Category.assoc, Iso.hom_inv_id_assoc]
  have hciB : (p ≫ (mapDomain (A.grading U.1) (B.grading U.1) (φ.sectionHom U.1)).ι) ≫
      (relativeProj B).chart U.1 U.2 = pieceIncl (ψ.comp φ) U ≫ m := by
    rw [← hgmψ, Category.assoc, ← hkey, ← Category.assoc, htψ, Category.assoc, hm₂]
  have htφ : (p ≫ (chartDomainIso φ U).hom) ≫ pieceIncl φ U =
      pieceIncl (ψ.comp φ) U ≫ a := by
    rw [← cancel_mono φ.relativeMapDomain.ι]
    simp only [Category.assoc]
    rw [hm₁, pieceIncl_comp_ι φ U, Iso.hom_inv_id_assoc, ← Category.assoc]
    exact hciB
  exact comp_chart_of φ ψ n U a b ha hm₁ hm₂ hc p j (p ≫ (chartDomainIso φ U).hom)
    (j ≫ (chartDomainIso ψ U).hom) htφ hrφ htψ hrψ rfl hgdφ
    ((Category.assoc _ _ _).trans (pieceIncl_comp_relativeMapHom (ψ.comp φ) U).symm) rfl hgmψ
    hciB rfl hgiψ ((Category.assoc _ _ _).trans (pieceIncl_comp_ι (ψ.comp φ) U).symm) hf

/-! ### Tag 07ZH's third assertion -/

/-- **Tag 07ZH's third assertion, in the vocabulary of `legTransport`.** Let `a` and `b` be
morphisms from `U(ψ ∘ φ)` to `U(φ)` and to `U(ψ)` whose composites with `r_φ`, with the inclusion
of `U(φ)` and `r_ψ`, and with the inclusion of `U(ψ)` are `r_{ψ ∘ φ}`, agree, and are the inclusion
of `U(ψ ∘ φ)`. Then `θ_φ` transported along `a` followed by `θ_ψ` transported along `b` is
`θ_{ψ ∘ φ}`.

The proof is `Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeTwistMap_unique`: both sides restrict
on the piece of `U(ψ ∘ φ)` over an affine open of the base to the affine-local comparison map, the
left side because the comparison maps of Tag 01MY for the three induced homomorphisms of graded
rings of sections compose, which is Tag 01MZ's third assertion. -/
public theorem relativeTwistMap_comp_of (n : ℤ)
    (a : (ψ.comp φ).relativeMapDomain.toScheme ⟶ φ.relativeMapDomain.toScheme)
    (b : (ψ.comp φ).relativeMapDomain.toScheme ⟶ ψ.relativeMapDomain.toScheme)
    (ha : a ≫ relativeMapHom φ = relativeMapHom (ψ.comp φ))
    {m : (ψ.comp φ).relativeMapDomain.toScheme ⟶ (relativeProj B).scheme}
    (hm₁ : a ≫ φ.relativeMapDomain.ι = m) (hm₂ : b ≫ relativeMapHom ψ = m)
    (hc : b ≫ ψ.relativeMapDomain.ι = (ψ.comp φ).relativeMapDomain.ι) :
    legTransport a (relativeTwistMap φ n) ha hm₁ ≫
        legTransport b (relativeTwistMap ψ n) hm₂ hc =
      relativeTwistMap (ψ.comp φ) n := by
  refine relativeTwistMap_unique (ψ.comp φ) n (fun U => ?_)
    (relativeTwistMap_chart (ψ.comp φ) n)
  refine Eq.trans ?_ (relativeTwistMap_chart (ψ.comp φ) n U)
  exact pullback_map_eq_of_legTransport_eq (pieceIncl (ψ.comp φ) U) rfl rfl
    (comp_chart φ ψ n U a b ha hm₁ hm₂ hc)

/-- **Stacks Project, Tag 07ZH.** *Assertion (3): the maps on twists of a composite compose.*

Let `a` be a morphism from `U(ψ ∘ φ)` to `U(φ)` which, followed by the inclusion of `U(φ)`, is the
inclusion of `U(ψ ∘ φ)` into `U(ψ)` followed by `r_ψ`; by Tag 07ZH's second assertion `r_{ψ ∘ φ}`
is then `a` followed by `r_φ`. The `n`-th map on twists of the composite is the inverse image along
`a` of the `n`-th map on twists of `φ` followed by the inverse image along the inclusion of
`U(ψ ∘ φ)` into `U(ψ)` of the `n`-th map on twists of `ψ` — the nine factors being those two
inverse images together with the pseudofunctoriality identifications of the inverse image for the
two legs, as in Tag 01MZ's third assertion.

`a` is unique with that property, because the inclusion of an open subscheme is a monomorphism;
`Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeTwistMap_comp` is this at the canonical `a`. -/
public theorem relativeTwistMap_comp' (n : ℤ)
    (a : (ψ.comp φ).relativeMapDomain.toScheme ⟶ φ.relativeMapDomain.toScheme)
    (ha : a ≫ relativeMapHom φ = relativeMapHom (ψ.comp φ))
    (hm : a ≫ φ.relativeMapDomain.ι =
      (relativeProj C).scheme.homOfLE (RelativeProjMapComp.relativeMapDomain_comp_le φ ψ) ≫
        relativeMapHom ψ) :
    (Scheme.Modules.pullbackCongr ha).inv.app (relativeTwist A n) ≫
        (Scheme.Modules.pullbackComp a (relativeMapHom φ)).inv.app (relativeTwist A n) ≫
        (Scheme.Modules.pullback a).map (relativeTwistMap φ n) ≫
        (Scheme.Modules.pullbackComp a φ.relativeMapDomain.ι).hom.app (relativeTwist B n) ≫
        (Scheme.Modules.pullbackCongr hm).hom.app (relativeTwist B n) ≫
        (Scheme.Modules.pullbackComp
          ((relativeProj C).scheme.homOfLE
            (RelativeProjMapComp.relativeMapDomain_comp_le φ ψ))
          (relativeMapHom ψ)).inv.app (relativeTwist B n) ≫
        (Scheme.Modules.pullback ((relativeProj C).scheme.homOfLE
          (RelativeProjMapComp.relativeMapDomain_comp_le φ ψ))).map (relativeTwistMap ψ n) ≫
        (Scheme.Modules.pullbackComp ((relativeProj C).scheme.homOfLE
            (RelativeProjMapComp.relativeMapDomain_comp_le φ ψ))
          ψ.relativeMapDomain.ι).hom.app (relativeTwist C n) ≫
        (Scheme.Modules.pullbackCongr (Scheme.homOfLE_ι (relativeProj C).scheme
          (RelativeProjMapComp.relativeMapDomain_comp_le φ ψ))).hom.app (relativeTwist C n) =
      relativeTwistMap (ψ.comp φ) n := by
  refine Eq.trans ?_ (relativeTwistMap_comp_of φ ψ n a
    ((relativeProj C).scheme.homOfLE (RelativeProjMapComp.relativeMapDomain_comp_le φ ψ)) ha hm
    rfl (Scheme.homOfLE_ι _ _))
  rw [legTransport_def, legTransport_def, pullbackCongr_inv_app_self]
  simp only [Category.id_comp, Category.assoc]

/-- **The restriction of `r_ψ` to `U(ψ ∘ φ)`**, as a morphism into `U(φ)`: the morphism `q` of Tag
07ZH's second assertion at the canonical identification of `U(ψ ∘ φ)` with `r_ψ^{-1}(U(φ))`. -/
public def relativeMapHomRestrict :
    (ψ.comp φ).relativeMapDomain.toScheme ⟶ φ.relativeMapDomain.toScheme :=
  (ψ.relativeMapDomain.ι.isoImage (relativeMapHom ψ ⁻¹ᵁ φ.relativeMapDomain) ≪≫
      (relativeProj C).scheme.isoOfEq
        (RelativeProjMapComp.relativeMapDomain_comp φ ψ).symm).inv ≫
    (relativeMapHom ψ ∣_ φ.relativeMapDomain)

/-- **The restriction of `r_ψ` to `U(ψ ∘ φ)`, followed by the inclusion of `U(φ)`**, is the
inclusion of `U(ψ ∘ φ)` into `U(ψ)` followed by `r_ψ`. -/
public theorem relativeMapHomRestrict_comp_ι :
    relativeMapHomRestrict φ ψ ≫ φ.relativeMapDomain.ι =
      (relativeProj C).scheme.homOfLE (RelativeProjMapComp.relativeMapDomain_comp_le φ ψ) ≫
        relativeMapHom ψ := by
  have hinv : (ψ.relativeMapDomain.ι.isoImage (relativeMapHom ψ ⁻¹ᵁ φ.relativeMapDomain) ≪≫
        (relativeProj C).scheme.isoOfEq
          (RelativeProjMapComp.relativeMapDomain_comp φ ψ).symm).inv ≫
      (relativeMapHom ψ ⁻¹ᵁ φ.relativeMapDomain).ι =
      (relativeProj C).scheme.homOfLE (RelativeProjMapComp.relativeMapDomain_comp_le φ ψ) := by
    rw [← cancel_mono ψ.relativeMapDomain.ι]
    simp only [Iso.trans_inv, Category.assoc, Scheme.Opens.isoImage_ι_inv_ι,
      Scheme.isoOfEq_inv_ι, Scheme.homOfLE_ι]
  rw [relativeMapHomRestrict, Category.assoc, morphismRestrict_ι, ← Category.assoc, hinv]

/-- **The restriction of `r_ψ` to `U(ψ ∘ φ)`, followed by `r_φ`**, is `r_{ψ ∘ φ}`. This is Tag
07ZH's second assertion. -/
public theorem relativeMapHomRestrict_comp_relativeMapHom :
    relativeMapHomRestrict φ ψ ≫ relativeMapHom φ = relativeMapHom (ψ.comp φ) :=
  (RelativeProjMapComp.relativeMapHom_comp' φ ψ (relativeMapHomRestrict φ ψ)
    (relativeMapHomRestrict_comp_ι φ ψ)).symm

/-- **Stacks Project, Tag 07ZH.** *Assertion (3), at the canonical morphisms.*

The `n`-th map on twists of a composite is the inverse image along the restriction of `r_ψ` to
`U(ψ ∘ φ)` of the `n`-th map on twists of `φ`, followed by the inverse image along the inclusion of
`U(ψ ∘ φ)` into `U(ψ)` of the `n`-th map on twists of `ψ`. -/
public theorem relativeTwistMap_comp (n : ℤ) :
    (Scheme.Modules.pullbackCongr
          (relativeMapHomRestrict_comp_relativeMapHom φ ψ)).inv.app (relativeTwist A n) ≫
        (Scheme.Modules.pullbackComp (relativeMapHomRestrict φ ψ)
          (relativeMapHom φ)).inv.app (relativeTwist A n) ≫
        (Scheme.Modules.pullback (relativeMapHomRestrict φ ψ)).map (relativeTwistMap φ n) ≫
        (Scheme.Modules.pullbackComp (relativeMapHomRestrict φ ψ)
          φ.relativeMapDomain.ι).hom.app (relativeTwist B n) ≫
        (Scheme.Modules.pullbackCongr
          (relativeMapHomRestrict_comp_ι φ ψ)).hom.app (relativeTwist B n) ≫
        (Scheme.Modules.pullbackComp
          ((relativeProj C).scheme.homOfLE
            (RelativeProjMapComp.relativeMapDomain_comp_le φ ψ))
          (relativeMapHom ψ)).inv.app (relativeTwist B n) ≫
        (Scheme.Modules.pullback ((relativeProj C).scheme.homOfLE
          (RelativeProjMapComp.relativeMapDomain_comp_le φ ψ))).map (relativeTwistMap ψ n) ≫
        (Scheme.Modules.pullbackComp ((relativeProj C).scheme.homOfLE
            (RelativeProjMapComp.relativeMapDomain_comp_le φ ψ))
          ψ.relativeMapDomain.ι).hom.app (relativeTwist C n) ≫
        (Scheme.Modules.pullbackCongr (Scheme.homOfLE_ι (relativeProj C).scheme
          (RelativeProjMapComp.relativeMapDomain_comp_le φ ψ))).hom.app (relativeTwist C n) =
      relativeTwistMap (ψ.comp φ) n :=
  relativeTwistMap_comp' φ ψ n (relativeMapHomRestrict φ ψ)
    (relativeMapHomRestrict_comp_relativeMapHom φ ψ) (relativeMapHomRestrict_comp_ι φ ψ)

end Comp

end Stacks.AlgebraicGeometry.Tag07ZGTwist

end
