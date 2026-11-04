module

public import StacksFrontier.AlgebraicGeometry.Morphism.TwistNested

/-!
# Tag 07ZG, assertion (3): the affine-local comparison maps agree on overlaps

`Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeTwistChart` is the affine-local comparison map of
Tag 07ZG's assertion (3): over the piece of `U(ψ)` over an affine open `U` of the base it is Tag
01MY's comparison map `θ` for the induced homomorphism `Γ(U, A) ⟶ Γ(U, B)`, conjugated by the
identifications of the source and the target with the inverse images of the two absolute twists.

This file proves that these maps agree on nested overlaps: for affine opens `T ⊆ U` of the base,
the comparison map over `U`, pulled back along the inclusion of the piece over `T` into the piece
over `U`, is the comparison map over `T`.

## Main results

* `Stacks.AlgebraicGeometry.Tag07ZGTwist.chartSourceIso_hom_eq` and `chartTargetIso_hom_eq`: the
  identifications of the source and the target of the affine-local comparison map, read at the
  single leg out of the piece which identifies the piece with the absolute domain of definition.
* `Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeTwistChart_comp_target`: the affine-local
  comparison map, with both chart identifications read at that leg, is Tag 01MY's comparison map
  read at the legs out of the piece.
* `Stacks.AlgebraicGeometry.Tag07ZGTwist.twistMapAt_nested_leg`: the nested compatibility of Tag
  01MY's comparison maps, read at an arbitrary leg.
* `Stacks.AlgebraicGeometry.Tag07ZGTwist.pullbackCongr_pullbackComp_leg` and
  `prefix_nested_rearrange`: the associativity coherence of the inverse image for a leg presented
  in two steps.
* `Stacks.AlgebraicGeometry.Tag07ZGTwist.nested_of_comp_target`: the nested agreement of two
  conjugated morphisms, at the level of variables.
* `Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeTwistChart_nested`: the affine-local comparison
  maps agree on a nested overlap.

## Implementation notes

Several steps are shaped by the kernel's deterministic budget.

* The statement comparing the transported chart identifications over the two members of a nested
  pair exceeds the budget on its own, so `nested_of_comp_target` takes every four-factor transport
  as a variable and they occur only inside the proof of `relativeTwistChart_nested`.
* The affine opens of the base are indexed by `AlgebraicGeometry.Scheme.affineOpens` throughout:
  converting a statement of this size to the spelling
  `Stacks.AlgebraicGeometry.RelativeProjMapDomain.AffineOpen` costs the whole budget.
* Projective spectra are indexed by their graded rings rather than carried as schemes, so that the
  kernel checks `Stacks.AlgebraicGeometry.ProjTwistCompare.twistingSheaf 𝒜 n` at the type
  `(AlgebraicGeometry.Proj 𝒜).Modules` once, against a variable.
* At the concrete inverse images here, `(a ≪≫ b ≪≫ c ≪≫ d).hom` is not convertible to
  `a.hom ≫ b.hom ≫ c.hom ≫ d.hom` within the budget; `natIso_trans₄_hom` takes that step once,
  against variables, and `chartSourceIso_hom_eq0` and `chartTargetIso_hom_eq0` are its instances.

## References

* [Stacks Project, Tag 07ZG](https://stacks.math.columbia.edu/tag/07ZG)
* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 01MZ](https://stacks.math.columbia.edu/tag/01MZ)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjShared
open Stacks.AlgebraicGeometry.ProjTwistChain
open Stacks.AlgebraicGeometry.ProjTwistCompare
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjTwists
open Stacks.AlgebraicGeometry.RelativeProjMapDomain
open Stacks.AlgebraicGeometry.Tag07ZGMorphism

namespace Stacks.AlgebraicGeometry.Tag07ZGTwist

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

universe u

/-! ### The three-factor transport at a composed leg -/

section Pseudo

attribute [local implicit_reducible] AlgebraicGeometry.Proj

variable {W' W V X : Scheme.{u}}

/-- **The three-factor transport of a morphism out of an inverse image, at a leg which is itself a
composite.** Reading the transport at the composed leg `w ≫ q` and then undoing the
pseudofunctoriality identification of `w` and `q` is the transport at the leg `w` of the morphism
`q` presents. -/
public theorem pullback_three_leg_of_comp (w : W' ⟶ W) (q : W ⟶ V) (a : V ⟶ X)
    {M : X.Modules} {N : V.Modules} (t : (Scheme.Modules.pullback a).obj M ⟶ N)
    {c : W' ⟶ X} (hc : (w ≫ q) ≫ a = c) (hwc : c = w ≫ q ≫ a) :
    (Scheme.Modules.pullbackCongr hwc).hom.app M ≫
        (Scheme.Modules.pullbackComp w (q ≫ a)).inv.app M ≫
        (Scheme.Modules.pullback w).map
          ((Scheme.Modules.pullbackComp q a).inv.app M ≫ (Scheme.Modules.pullback q).map t) =
      ((Scheme.Modules.pullbackCongr hc).inv.app M ≫
          (Scheme.Modules.pullbackComp (w ≫ q) a).inv.app M ≫
          (Scheme.Modules.pullback (w ≫ q)).map t) ≫
        (Scheme.Modules.pullbackComp w q).inv.app N := by
  rw [show (Scheme.Modules.pullbackCongr hwc).hom.app M =
      (Scheme.Modules.pullbackCongr hwc.symm).inv.app M from rfl,
    pullback_three_comp_leg w q a t rfl hc hwc.symm]
  simp only [pullbackCongr_refl_eq, Iso.refl_inv, NatTrans.id_app, Category.id_comp,
    Category.assoc, Iso.hom_inv_id_app, Functor.comp_obj, Category.comp_id]

/-- **The underlying morphism of a four-fold composite of isomorphisms**, at the level of
variables. At the concrete inverse images below this step exceeds the kernel's deterministic
budget, so it is taken once here and each concrete instance is a substitution. -/
public theorem natIso_trans₄_hom {𝒞 𝒟 ℰ ℱ : Type*} [Category 𝒞] [Category 𝒟] [Category ℰ]
    [Category ℱ] (F : ℰ ⥤ 𝒟) (G : ℱ ⥤ ℰ) (H : 𝒞 ⥤ ℱ) {K : 𝒞 ⥤ ℰ} {P₁ P₂ P₃ : 𝒞 ⥤ 𝒟}
    (a : P₁ ≅ P₂) (b : P₂ ≅ P₃) (c : K ⋙ F ≅ P₃) (d : H ⋙ G ≅ K) (M : 𝒞) {Tw : ℱ}
    (e : H.obj M ≅ Tw) :
    (a.app M ≪≫ b.app M ≪≫ (c.app M).symm ≪≫
        F.mapIso ((d.app M).symm ≪≫ G.mapIso e)).hom =
      a.hom.app M ≫ b.hom.app M ≫ c.inv.app M ≫ F.map (d.inv.app M ≫ G.map e.hom) :=
  rfl

/-- **Undoing an isomorphism presented as a composite whose second factor has a retraction.** If
`E.hom` is `p` followed by `q` and `q` is followed by `r` to the identity, then `E.inv` followed by
`p` is `r`. -/
public theorem inv_comp_eq_of_hom_eq {C : Type*} [Category C] {X Y Z : C} (E : X ≅ Y)
    (p : X ⟶ Z) (q : Z ⟶ Y) (r : Y ⟶ Z) (hE : E.hom = p ≫ q) (hqr : q ≫ r = 𝟙 Z) :
    E.inv ≫ p = r :=
  calc E.inv ≫ p = E.inv ≫ p ≫ q ≫ r := by rw [hqr, Category.comp_id]
    _ = E.inv ≫ E.hom ≫ r := by rw [hE, Category.assoc]
    _ = r := by rw [Iso.inv_hom_id_assoc]

/-- **The pseudofunctoriality identifications of a leg presented in two steps.** Undoing the
identification of an equal leg and then the one of the two steps, and then applying inside the
first step the identification of the second step with the morphism it maps to, is the
identification of the composed leg undone one factor at a time. -/
@[reassoc]
public theorem pullbackCongr_pullbackComp_leg {W Z V X : Scheme.{u}} (k : W ⟶ Z) (g : Z ⟶ V)
    (r : V ⟶ X) {gT : W ⟶ V} (hk : k ≫ g = gT) (hkc : k ≫ g ≫ r = gT ≫ r) (Mt : X.Modules) :
    (Scheme.Modules.pullbackCongr hk).inv.app ((Scheme.Modules.pullback r).obj Mt) ≫
        (Scheme.Modules.pullbackComp k g).inv.app ((Scheme.Modules.pullback r).obj Mt) ≫
        (Scheme.Modules.pullback k).map ((Scheme.Modules.pullbackComp g r).hom.app Mt) =
      (Scheme.Modules.pullbackComp gT r).hom.app Mt ≫
        (Scheme.Modules.pullbackCongr hkc).inv.app Mt ≫
        (Scheme.Modules.pullbackComp k (g ≫ r)).inv.app Mt := by
  subst hk
  obtain rfl : hkc = (Category.assoc k g r).symm := Subsingleton.elim _ _
  rw [pullbackCongr_refl_eq]
  simp only [Iso.refl_inv, NatTrans.id_app, Category.id_comp]
  rw [show (Scheme.Modules.pullbackCongr (Category.assoc k g r).symm).inv.app Mt =
      (Scheme.Modules.pullbackCongr (Category.assoc k g r)).hom.app Mt from rfl,
    ← pullbackComp_hom_app_comp_map_assoc k g r Mt, Iso.hom_inv_id_app]
  simp only [Functor.comp_obj, Category.comp_id]

/-- **The nested transport of a morphism out of an inverse image, with the pseudofunctoriality
identification of the leg's two steps moved across.** The identification of the leg over the
smaller member followed by the nested transport is the identification of the equal leg and of the
two steps, followed by the inverse image of the identification over the larger member together
with the morphism transported there. -/
public theorem prefix_nested_rearrange {W Z V X : Scheme.{u}} (k : W ⟶ Z) (g : Z ⟶ V)
    (r : V ⟶ X) {gT : W ⟶ V} (hk : k ≫ g = gT) (hkc : k ≫ g ≫ r = gT ≫ r) (Mt : X.Modules)
    {Q : Z.Modules} (Y : (Scheme.Modules.pullback (g ≫ r)).obj Mt ⟶ Q)
    {R : W.Modules} (tail : (Scheme.Modules.pullback k).obj Q ⟶ R) :
    (Scheme.Modules.pullbackComp gT r).hom.app Mt ≫
        ((Scheme.Modules.pullbackCongr hkc).inv.app Mt ≫
          (Scheme.Modules.pullbackComp k (g ≫ r)).inv.app Mt ≫
          (Scheme.Modules.pullback k).map Y ≫ tail) =
      (Scheme.Modules.pullbackCongr hk).inv.app ((Scheme.Modules.pullback r).obj Mt) ≫
        (Scheme.Modules.pullbackComp k g).inv.app ((Scheme.Modules.pullback r).obj Mt) ≫
        (Scheme.Modules.pullback k).map
          ((Scheme.Modules.pullbackComp g r).hom.app Mt ≫ Y) ≫ tail := by
  simp only [Functor.map_comp, Category.assoc]
  rw [pullbackCongr_pullbackComp_leg_assoc k g r hk hkc Mt]

/-- **The congruence isomorphism of the inverse image at a reflexive equality is absorbed.** The
module is an explicit argument, so that a rewrite with this equation has nothing to infer in that
position. -/
public theorem congr_refl_inv_app_comp {X' Y' : Scheme.{u}} {f : X' ⟶ Y'}
    (M : Y'.Modules) {Q : X'.Modules} (z : (Scheme.Modules.pullback f).obj M ⟶ Q) :
    (Scheme.Modules.pullbackCongr (rfl : f = f)).inv.app M ≫ z = z := by
  rw [pullbackCongr_refl_eq]
  exact Category.id_comp z

/-- The same congruence isomorphism read on the other side: its component at a module is the
identity. -/
public theorem congr_refl_hom_app_eq {X' Y' : Scheme.{u}} {f : X' ⟶ Y'}
    (M : Y'.Modules) :
    (Scheme.Modules.pullbackCongr (rfl : f = f)).hom.app M =
      𝟙 ((Scheme.Modules.pullback f).obj M) := by
  rw [pullbackCongr_refl_eq]
  rfl

/-- Congruence in the second factor of a composite, with a beta-reduced statement (unlike
`congrArg` with a lambda). -/
public theorem comp_congr_right {C : Type*} [Category C] {X Y Z : C} (a : X ⟶ Y) {f g : Y ⟶ Z}
    (hfg : f = g) : a ≫ f = a ≫ g := by
  rw [hfg]

/-- **Cancelling a morphism with a right inverse.** -/
public theorem eq_of_comp_right_cancel {C : Type*} [Category C] {X Y Z : C} {f g : X ⟶ Y}
    (t : Y ⟶ Z) (s : Z ⟶ Y) (hts : t ≫ s = 𝟙 Y) (hfg : f ≫ t = g ≫ t) : f = g := by
  rw [← Category.comp_id f, ← hts, ← Category.assoc, hfg, Category.assoc, hts, Category.comp_id]

/-- **Two factorizations of a square spliced.** If `e ≫ q` is `m ≫ b` and `r ≫ t` is `q ≫ rB`,
then `m` followed by `b ≫ rB` is `e ≫ r` followed by `t`. -/
public theorem splice_of_comp {C : Type*} [Category C] {X₀ X₁ X₂ X₃ X₄ X₅ : C}
    {e : X₀ ⟶ X₁} {q : X₁ ⟶ X₂} {m : X₀ ⟶ X₃} {b : X₃ ⟶ X₂}
    {r : X₁ ⟶ X₄} {t : X₄ ⟶ X₅} {rB : X₂ ⟶ X₅}
    (hq : e ≫ q = m ≫ b) (hnest : r ≫ t = q ≫ rB) :
    m ≫ b ≫ rB = (e ≫ r) ≫ t := by
  rw [Category.assoc, hnest, ← Category.assoc, ← hq, Category.assoc]

/-- **The nested agreement of two conjugated morphisms, at the level of variables.** Let `pU` and
`pT` be two morphisms into a scheme with `k ≫ pU = pT`, let `cmpU` and `cmpT` be
endomorphism-shaped morphisms between the inverse images of two sheaves of modules along them, and
suppose each is conjugate to a third morphism by an identification of its source and one of its
target: `cmpU` to `tU` by `srcU` and `tgtU`, and `cmpT` to `tT` by `srcT` and `tgtT`, where `tgtT`
has a right inverse. If the two identifications over the smaller member are the ones over the
larger pulled back along `k` and followed by `tailA` and `tailB`, and if `tU` and `tT` are
compatible with those two tails, then `cmpT` is `cmpU` pulled back along `k`. -/
public theorem nested_of_comp_target {D PU PT : Scheme.{u}} {Mm Nn : D.Modules}
    {pU : PU ⟶ D} {pT : PT ⟶ D} (k : PT ⟶ PU) (hk : k ≫ pU = pT)
    {αU βU : PU.Modules} {αT βT : PT.Modules}
    {cmpU : (Scheme.Modules.pullback pU).obj Mm ⟶ (Scheme.Modules.pullback pU).obj Nn}
    {cmpT : (Scheme.Modules.pullback pT).obj Mm ⟶ (Scheme.Modules.pullback pT).obj Nn}
    {srcU : (Scheme.Modules.pullback pU).obj Mm ⟶ αU}
    {tgtU : (Scheme.Modules.pullback pU).obj Nn ⟶ βU} {tU : αU ⟶ βU}
    {srcT : (Scheme.Modules.pullback pT).obj Mm ⟶ αT}
    {tgtT : (Scheme.Modules.pullback pT).obj Nn ⟶ βT} {tT : αT ⟶ βT}
    {tailA : (Scheme.Modules.pullback k).obj αU ⟶ αT}
    {tailB : (Scheme.Modules.pullback k).obj βU ⟶ βT}
    {s : βT ⟶ (Scheme.Modules.pullback pT).obj Nn}
    (hs : tgtT ≫ s = 𝟙 ((Scheme.Modules.pullback pT).obj Nn))
    (hU : cmpU ≫ tgtU = srcU ≫ tU) (hT : cmpT ≫ tgtT = srcT ≫ tT)
    (hsrc : srcT = (Scheme.Modules.pullbackCongr hk).inv.app Mm ≫
      (Scheme.Modules.pullbackComp k pU).inv.app Mm ≫
      (Scheme.Modules.pullback k).map srcU ≫ tailA)
    (htgt : tgtT = (Scheme.Modules.pullbackCongr hk).inv.app Nn ≫
      (Scheme.Modules.pullbackComp k pU).inv.app Nn ≫
      (Scheme.Modules.pullback k).map tgtU ≫ tailB)
    (hsplice : (Scheme.Modules.pullback k).map tU ≫ tailB = tailA ≫ tT) :
    (Scheme.Modules.pullbackCongr hk).inv.app Mm ≫
        (Scheme.Modules.pullbackComp k pU).inv.app Mm ≫
        (Scheme.Modules.pullback k).map cmpU ≫
        (Scheme.Modules.pullbackComp k pU).hom.app Nn ≫
        (Scheme.Modules.pullbackCongr hk).hom.app Nn = cmpT := by
  refine eq_of_comp_right_cancel tgtT s hs ?_
  rw [hT, htgt, hsrc]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [← Functor.map_comp_assoc, hU, Functor.map_comp_assoc, hsplice]

/-- **A morphism presented as the first factor of an isomorphism has a right inverse.** -/
public theorem comp_eq_id_of_hom_eq {C : Type*} [Category C] {X Y Z : C} (E : X ≅ Y)
    (p : X ⟶ Z) (q : Z ⟶ Y) (hE : E.hom = p ≫ q) : p ≫ q ≫ E.inv = 𝟙 X := by
  rw [← Category.assoc, ← hE, E.hom_inv_id]

end Pseudo

/-! ### The transports at a leg into a projective spectrum -/

section Legs

attribute [local implicit_reducible] AlgebraicGeometry.Proj

universe w w'

variable {R₁ R₂ : Type u} {σ : Type w} {τ : Type w'}
  [CommRing R₁] [CommRing R₂]
  [SetLike σ R₁] [AddSubgroupClass σ R₁]
  [SetLike τ R₂] [AddSubgroupClass τ R₂]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]

/-- `pullback_three_leg_of_comp` with the leg into a projective spectrum and the target of the
transported morphism the absolute `n`-th twist, and with a further morphism prefixed. -/
public theorem pullback_three_leg_of_comp_proj (n : ℤ) {W' W X : Scheme.{u}}
    (w : W' ⟶ W) (q : W ⟶ AlgebraicGeometry.Proj 𝒜) (a : AlgebraicGeometry.Proj 𝒜 ⟶ X)
    {M : X.Modules} (t : (Scheme.Modules.pullback a).obj M ⟶ twistingSheaf 𝒜 n)
    {P : W'.Modules} {c : W' ⟶ X} (e : P ⟶ (Scheme.Modules.pullback c).obj M)
    (hc : (w ≫ q) ≫ a = c) (hwc : c = w ≫ q ≫ a) :
    e ≫ (Scheme.Modules.pullbackCongr hwc).hom.app M ≫
        (Scheme.Modules.pullbackComp w (q ≫ a)).inv.app M ≫
        (Scheme.Modules.pullback w).map
          ((Scheme.Modules.pullbackComp q a).inv.app M ≫ (Scheme.Modules.pullback q).map t) =
      (e ≫ (Scheme.Modules.pullbackCongr hc).inv.app M ≫
          (Scheme.Modules.pullbackComp (w ≫ q) a).inv.app M ≫
          (Scheme.Modules.pullback (w ≫ q)).map t) ≫
        (Scheme.Modules.pullbackComp w q).inv.app (twistingSheaf 𝒜 n) :=
  (congrArg (fun z => e ≫ z) (pullback_three_leg_of_comp w q a t hc hwc)).trans
    (Category.assoc _ _ _).symm

/-- **Tag 01MY's comparison map at a pair of legs presented tautologically**: the three factors
that do not name the legs, the two congruence isomorphisms having become identities. -/
public theorem twistMapAt_refl (φ : 𝒜 →+*ᵍ ℬ) (n : ℤ) {W : Scheme.{u}}
    (q : W ⟶ (mapDomain 𝒜 ℬ φ).toScheme) :
    twistMapAt 𝒜 ℬ φ n q rfl rfl =
      (Scheme.Modules.pullbackComp q (mapHom 𝒜 ℬ φ)).inv.app (twistingSheaf 𝒜 n) ≫
        (Scheme.Modules.pullback q).map (twistMap 𝒜 ℬ φ n) ≫
        (Scheme.Modules.pullbackComp q (mapDomain 𝒜 ℬ φ).ι).hom.app (twistingSheaf ℬ n) :=
  rfl

/-- Cancelling the pseudofunctoriality identification of a pair of legs into a projective spectrum
against itself, after an arbitrary morphism. -/
public theorem comp_pullbackComp_inv_hom_app (n : ℤ) {W V : Scheme.{u}} (q : W ⟶ V)
    (b : V ⟶ AlgebraicGeometry.Proj 𝒜) {P : W.Modules}
    (z : P ⟶ (Scheme.Modules.pullback (q ≫ b)).obj (twistingSheaf 𝒜 n)) :
    z ≫ (Scheme.Modules.pullbackComp q b).inv.app (twistingSheaf 𝒜 n) ≫
        (Scheme.Modules.pullbackComp q b).hom.app (twistingSheaf 𝒜 n) = z :=
  (congrArg (fun y => z ≫ y)
      (Iso.inv_hom_id_app (Scheme.Modules.pullbackComp q b) (twistingSheaf 𝒜 n))).trans
    (Category.comp_id z)

/-- Cancelling the pseudofunctoriality identification of a pair of legs into a projective spectrum
against itself, in the other order. -/
public theorem comp_pullbackComp_hom_inv_app (n : ℤ) {W V : Scheme.{u}} (q : W ⟶ V)
    (b : V ⟶ AlgebraicGeometry.Proj 𝒜) {P : W.Modules}
    (z : P ⟶ (Scheme.Modules.pullback b ⋙ Scheme.Modules.pullback q).obj
      (twistingSheaf 𝒜 n)) :
    z ≫ (Scheme.Modules.pullbackComp q b).hom.app (twistingSheaf 𝒜 n) ≫
        (Scheme.Modules.pullbackComp q b).inv.app (twistingSheaf 𝒜 n) = z :=
  (congrArg (fun y => z ≫ y)
      (Iso.hom_inv_id_app (Scheme.Modules.pullbackComp q b) (twistingSheaf 𝒜 n))).trans
    (Category.comp_id z)

/-- Cancelling the pseudofunctoriality identification of a pair of legs into a projective spectrum
against itself, with an arbitrary morphism following. -/
public theorem pullbackComp_hom_inv_app_comp (n : ℤ) {W V : Scheme.{u}} (q : W ⟶ V)
    (b : V ⟶ AlgebraicGeometry.Proj 𝒜) {P : W.Modules}
    (z : (Scheme.Modules.pullback b ⋙ Scheme.Modules.pullback q).obj (twistingSheaf 𝒜 n) ⟶ P) :
    (Scheme.Modules.pullbackComp q b).hom.app (twistingSheaf 𝒜 n) ≫
        (Scheme.Modules.pullbackComp q b).inv.app (twistingSheaf 𝒜 n) ≫ z = z :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun y => y ≫ z)
        (Iso.hom_inv_id_app (Scheme.Modules.pullbackComp q b) (twistingSheaf 𝒜 n))).trans
      (Category.id_comp z))

/-- **Tag 01MY's comparison map at a leg precomposed with a further morphism, with both composed
legs taken tautologically.** The pseudofunctoriality identification of the further morphism and the
leg into the source spectrum, followed by the comparison map at the composed leg, is the inverse
image of the comparison map at the original leg followed by the pseudofunctoriality identification
of the further morphism and the leg into the target spectrum.

This is stated at the level of variables: at a concrete pair of affine opens of the base, `simp`
does not reach the component of an identity natural transformation at the absolute twist. -/
public theorem twistMapAt_comp_leg_refl (φ : 𝒜 →+*ᵍ ℬ) (n : ℤ) {W' W : Scheme.{u}} (w : W' ⟶ W)
    (q : W ⟶ (mapDomain 𝒜 ℬ φ).toScheme) :
    (Scheme.Modules.pullbackComp w (q ≫ mapHom 𝒜 ℬ φ)).hom.app (twistingSheaf 𝒜 n) ≫
        twistMapAt 𝒜 ℬ φ n (w ≫ q) (Category.assoc _ _ _) (Category.assoc _ _ _) =
      (Scheme.Modules.pullback w).map (twistMapAt 𝒜 ℬ φ n q rfl rfl) ≫
        (Scheme.Modules.pullbackComp w (q ≫ (mapDomain 𝒜 ℬ φ).ι)).hom.app
          (twistingSheaf ℬ n) := by
  rw [twistMapAt_comp_leg 𝒜 ℬ φ n w q rfl rfl (Category.assoc _ _ _) rfl
      (Category.assoc _ _ _) rfl,
    congr_refl_inv_app_comp (f := w ≫ q ≫ mapHom 𝒜 ℬ φ) (twistingSheaf 𝒜 n),
    congr_refl_hom_app_eq (f := w ≫ q ≫ (mapDomain 𝒜 ℬ φ).ι) (twistingSheaf ℬ n),
    Category.comp_id, pullbackComp_hom_inv_app_comp 𝒜 n w (q ≫ mapHom 𝒜 ℬ φ)]

/-- The pseudofunctoriality identification of a pair of legs into a projective spectrum cancels
against itself. -/
public theorem pullbackComp_inv_hom_id_app (n : ℤ) {W V : Scheme.{u}} (q : W ⟶ V)
    (b : V ⟶ AlgebraicGeometry.Proj 𝒜) :
    (Scheme.Modules.pullbackComp q b).inv.app (twistingSheaf 𝒜 n) ≫
        (Scheme.Modules.pullbackComp q b).hom.app (twistingSheaf 𝒜 n) =
      𝟙 ((Scheme.Modules.pullback (q ≫ b)).obj (twistingSheaf 𝒜 n)) :=
  Iso.inv_hom_id_app (Scheme.Modules.pullbackComp q b) (twistingSheaf 𝒜 n)

end Legs

variable {S : Scheme.{u}} {A B : SheafGradedAlgebra S} (ψ : SheafGradedAlgebraHom A B)

/-! ### The identifications of the source and the target, read at one leg -/

/-- **The identification of the source of the affine-local comparison map, written out as its four
factors.** -/
public theorem chartSourceIso_hom_eq0 (n : ℤ) (U : S.affineOpens) :
    (chartSourceIso ψ n U).hom =
      (Scheme.Modules.pullbackComp (pieceIncl ψ U) (relativeMapHom ψ)).hom.app
          (relativeTwist A n) ≫
        (Scheme.Modules.pullbackCongr (pieceIncl_comp_relativeMapHom ψ U)).hom.app
          (relativeTwist A n) ≫
        (Scheme.Modules.pullbackComp (chartDomainIso ψ U).inv
            (mapHom (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1) ≫
              (relativeProj A).chart U.1 U.2)).inv.app (relativeTwist A n) ≫
        (Scheme.Modules.pullback (chartDomainIso ψ U).inv).map
          ((Scheme.Modules.pullbackComp
                (mapHom (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1))
                ((relativeProj A).chart U.1 U.2)).inv.app (relativeTwist A n) ≫
            (Scheme.Modules.pullback
                (mapHom (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1))).map
              (chartTwistIso A n U).hom) :=
  natIso_trans₄_hom (Scheme.Modules.pullback (chartDomainIso ψ U).inv)
    (Scheme.Modules.pullback (mapHom (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1)))
    (Scheme.Modules.pullback ((relativeProj A).chart U.1 U.2))
    (Scheme.Modules.pullbackComp (pieceIncl ψ U) (relativeMapHom ψ))
    (Scheme.Modules.pullbackCongr (pieceIncl_comp_relativeMapHom ψ U))
    (Scheme.Modules.pullbackComp (chartDomainIso ψ U).inv
      (mapHom (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1) ≫
        (relativeProj A).chart U.1 U.2))
    (Scheme.Modules.pullbackComp (mapHom (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1))
      ((relativeProj A).chart U.1 U.2))
    (relativeTwist A n) (chartTwistIso A n U)

/-- **The identification of the source of the affine-local comparison map, read at the single leg
out of the piece.** The inverse image along the inclusion of the piece of the inverse image along
`r_ψ` of the `n`-th relative twist is identified with the inverse image of the absolute `n`-th
twist on `Proj Γ(U, A)` along the leg which is the identification of the piece with the absolute
domain of definition followed by the absolute morphism of Tag 01MY; the identification of
`Stacks.AlgebraicGeometry.Tag07ZGTwist.chartSourceIso` is that one followed by the
pseudofunctoriality identification of the two factors of the leg. -/
public theorem chartSourceIso_hom_eq (n : ℤ) (U : S.affineOpens)
    (hc : ((chartDomainIso ψ U).inv ≫
          mapHom (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1)) ≫
        (relativeProj A).chart U.1 U.2 = pieceIncl ψ U ≫ relativeMapHom ψ) :
    (chartSourceIso ψ n U).hom =
      ((Scheme.Modules.pullbackComp (pieceIncl ψ U) (relativeMapHom ψ)).hom.app
            (relativeTwist A n) ≫
          (Scheme.Modules.pullbackCongr hc).inv.app (relativeTwist A n) ≫
          (Scheme.Modules.pullbackComp
              ((chartDomainIso ψ U).inv ≫
                mapHom (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1))
              ((relativeProj A).chart U.1 U.2)).inv.app (relativeTwist A n) ≫
          (Scheme.Modules.pullback
              ((chartDomainIso ψ U).inv ≫
                mapHom (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1))).map
            (chartTwistIso A n U).hom) ≫
        (Scheme.Modules.pullbackComp (chartDomainIso ψ U).inv
            (mapHom (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1))).inv.app
          (twistingSheaf (A.grading U.1) n) :=
  (chartSourceIso_hom_eq0 ψ n U).trans
    (pullback_three_leg_of_comp_proj (A.grading U.1) n (chartDomainIso ψ U).inv
      (mapHom (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1))
      ((relativeProj A).chart U.1 U.2) (chartTwistIso A n U).hom
      ((Scheme.Modules.pullbackComp (pieceIncl ψ U) (relativeMapHom ψ)).hom.app
        (relativeTwist A n)) hc (pieceIncl_comp_relativeMapHom ψ U))

/-- **The identification of the target of the affine-local comparison map, written out as its four
factors.** -/
public theorem chartTargetIso_hom_eq0 (n : ℤ) (U : S.affineOpens) :
    (chartTargetIso ψ n U).hom =
      (Scheme.Modules.pullbackComp (pieceIncl ψ U) ψ.relativeMapDomain.ι).hom.app
          (relativeTwist B n) ≫
        (Scheme.Modules.pullbackCongr (pieceIncl_comp_ι ψ U)).hom.app
          (relativeTwist B n) ≫
        (Scheme.Modules.pullbackComp (chartDomainIso ψ U).inv
            ((mapDomain (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1)).ι ≫
              (relativeProj B).chart U.1 U.2)).inv.app (relativeTwist B n) ≫
        (Scheme.Modules.pullback (chartDomainIso ψ U).inv).map
          ((Scheme.Modules.pullbackComp
                (mapDomain (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1)).ι
                ((relativeProj B).chart U.1 U.2)).inv.app (relativeTwist B n) ≫
            (Scheme.Modules.pullback
                (mapDomain (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1)).ι).map
              (chartTwistIso B n U).hom) :=
  natIso_trans₄_hom (Scheme.Modules.pullback (chartDomainIso ψ U).inv)
    (Scheme.Modules.pullback (mapDomain (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1)).ι)
    (Scheme.Modules.pullback ((relativeProj B).chart U.1 U.2))
    (Scheme.Modules.pullbackComp (pieceIncl ψ U) ψ.relativeMapDomain.ι)
    (Scheme.Modules.pullbackCongr (pieceIncl_comp_ι ψ U))
    (Scheme.Modules.pullbackComp (chartDomainIso ψ U).inv
      ((mapDomain (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1)).ι ≫
        (relativeProj B).chart U.1 U.2))
    (Scheme.Modules.pullbackComp
      (mapDomain (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1)).ι
      ((relativeProj B).chart U.1 U.2))
    (relativeTwist B n) (chartTwistIso B n U)

/-- **The identification of the target of the affine-local comparison map, read at the single leg
out of the piece.** The companion of
`Stacks.AlgebraicGeometry.Tag07ZGTwist.chartSourceIso_hom_eq` for the inclusion of `U(ψ)` in place
of `r_ψ` and the inclusion of the absolute domain of definition in place of the absolute morphism
of Tag 01MY. -/
public theorem chartTargetIso_hom_eq (n : ℤ) (U : S.affineOpens)
    (hc : ((chartDomainIso ψ U).inv ≫
          (mapDomain (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1)).ι) ≫
        (relativeProj B).chart U.1 U.2 = pieceIncl ψ U ≫ ψ.relativeMapDomain.ι) :
    (chartTargetIso ψ n U).hom =
      ((Scheme.Modules.pullbackComp (pieceIncl ψ U) ψ.relativeMapDomain.ι).hom.app
            (relativeTwist B n) ≫
          (Scheme.Modules.pullbackCongr hc).inv.app (relativeTwist B n) ≫
          (Scheme.Modules.pullbackComp
              ((chartDomainIso ψ U).inv ≫
                (mapDomain (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1)).ι)
              ((relativeProj B).chart U.1 U.2)).inv.app (relativeTwist B n) ≫
          (Scheme.Modules.pullback
              ((chartDomainIso ψ U).inv ≫
                (mapDomain (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1)).ι)).map
            (chartTwistIso B n U).hom) ≫
        (Scheme.Modules.pullbackComp (chartDomainIso ψ U).inv
            (mapDomain (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1)).ι).inv.app
          (twistingSheaf (B.grading U.1) n) :=
  (chartTargetIso_hom_eq0 ψ n U).trans
    (pullback_three_leg_of_comp_proj (B.grading U.1) n (chartDomainIso ψ U).inv
      (mapDomain (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1)).ι
      ((relativeProj B).chart U.1 U.2) (chartTwistIso B n U).hom
      ((Scheme.Modules.pullbackComp (pieceIncl ψ U) ψ.relativeMapDomain.ι).hom.app
        (relativeTwist B n)) hc (pieceIncl_comp_ι ψ U))

/-! ### The affine-local comparison map read at the single leg out of the piece -/

/-- The affine-local comparison map, as the composite of its three factors. -/
public theorem relativeTwistChartDef (n : ℤ) (U : S.affineOpens) :
    relativeTwistChart ψ n U =
      (chartSourceIso ψ n U).hom ≫
        (Scheme.Modules.pullback (chartDomainIso ψ U).inv).map
          (twistMap (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1) n) ≫
        (chartTargetIso ψ n U).inv :=
  rfl

/-- **The affine-local comparison map, with both chart identifications read at the single leg out
of the piece.** The comparison map followed by the transported chart identification of the target
is the transported chart identification of the source followed by Tag 01MY's comparison map for
`Γ(U, A) ⟶ Γ(U, B)`, read at the leg which identifies the piece with the absolute domain of
definition. -/
public theorem relativeTwistChart_comp_target (n : ℤ) (U : S.affineOpens)
    (hc : ((chartDomainIso ψ U).inv ≫
          mapHom (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1)) ≫
        (relativeProj A).chart U.1 U.2 = pieceIncl ψ U ≫ relativeMapHom ψ)
    (hc' : ((chartDomainIso ψ U).inv ≫
          (mapDomain (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1)).ι) ≫
        (relativeProj B).chart U.1 U.2 = pieceIncl ψ U ≫ ψ.relativeMapDomain.ι) :
    relativeTwistChart ψ n U ≫
        ((Scheme.Modules.pullbackComp (pieceIncl ψ U) ψ.relativeMapDomain.ι).hom.app
            (relativeTwist B n) ≫
          (Scheme.Modules.pullbackCongr hc').inv.app (relativeTwist B n) ≫
          (Scheme.Modules.pullbackComp
              ((chartDomainIso ψ U).inv ≫
                (mapDomain (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1)).ι)
              ((relativeProj B).chart U.1 U.2)).inv.app (relativeTwist B n) ≫
          (Scheme.Modules.pullback
              ((chartDomainIso ψ U).inv ≫
                (mapDomain (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1)).ι)).map
            (chartTwistIso B n U).hom) =
      ((Scheme.Modules.pullbackComp (pieceIncl ψ U) (relativeMapHom ψ)).hom.app
            (relativeTwist A n) ≫
          (Scheme.Modules.pullbackCongr hc).inv.app (relativeTwist A n) ≫
          (Scheme.Modules.pullbackComp
              ((chartDomainIso ψ U).inv ≫
                mapHom (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1))
              ((relativeProj A).chart U.1 U.2)).inv.app (relativeTwist A n) ≫
          (Scheme.Modules.pullback
              ((chartDomainIso ψ U).inv ≫
                mapHom (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1))).map
            (chartTwistIso A n U).hom) ≫
        twistMapAt (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1) n
          (chartDomainIso ψ U).inv rfl rfl := by
  have hcancel := inv_comp_eq_of_hom_eq (chartTargetIso ψ n U) _
    ((Scheme.Modules.pullbackComp (chartDomainIso ψ U).inv
        (mapDomain (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1)).ι).inv.app
      (twistingSheaf (B.grading U.1) n))
    ((Scheme.Modules.pullbackComp (chartDomainIso ψ U).inv
        (mapDomain (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1)).ι).hom.app
      (twistingSheaf (B.grading U.1) n))
    (chartTargetIso_hom_eq ψ n U hc')
    (pullbackComp_inv_hom_id_app (B.grading U.1) n (chartDomainIso ψ U).inv
      (mapDomain (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1)).ι)
  rw [relativeTwistChartDef, comp₃_comp, hcancel, chartSourceIso_hom_eq ψ n U hc,
    twistMapAt_refl]
  exact Category.assoc _ _ _

/-! ### The nested compatibility of Tag 01MY's comparison maps at arbitrary legs -/

section NestedLeg

variable (T U : S.Opens) (h : T ≤ U) (hT : IsAffineOpen T) (hU : IsAffineOpen U) (n : ℤ)

/-- **The comparison maps of Tag 01MY over a nested pair of affine opens of the base are
compatible with the comparison maps of the restrictions, read at an arbitrary leg.**

This is `Stacks.AlgebraicGeometry.Tag07ZGTwist.twistMapAt_nested` with every one of its four
comparison maps read at a leg out of one further scheme `W`, presented by a morphism `w` into the
absolute domain of definition over `T`. The two intermediate legs — the one into `Proj Γ(U, A)` and
the one into `Proj Γ(U, B)` — are arguments pinned by the equations that present the four
presenting morphisms, so that the domains of definition do not occur in the type. -/
public theorem twistMapAt_nested_leg {W : Scheme.{u}}
    (w : W ⟶ (mapDomain (A.grading T) (B.grading T) (ψ.sectionHom T)).toScheme)
    {dk : W ⟶ AlgebraicGeometry.Proj (A.grading U)}
    {ik : W ⟶ AlgebraicGeometry.Proj (B.grading U)}
    (hwd : w ≫ mapHom (A.grading T) (B.grading T) (ψ.sectionHom T) ≫
      projInclusionMap A T U h hT hU = dk)
    (p : W ⟶ (mapDomain (A.grading U) (A.grading T) (A.res h)).toScheme)
    (hpd : p ≫ mapHom (A.grading U) (A.grading T) (A.res h) = dk)
    (hpm : p ≫ (mapDomain (A.grading U) (A.grading T) (A.res h)).ι =
      w ≫ mapHom (A.grading T) (B.grading T) (ψ.sectionHom T))
    (j : W ⟶ (mapDomain (B.grading U) (B.grading T) (B.res h)).toScheme)
    (hjm : j ≫ mapHom (B.grading U) (B.grading T) (B.res h) = ik)
    (hji : j ≫ (mapDomain (B.grading U) (B.grading T) (B.res h)).ι =
      w ≫ (mapDomain (A.grading T) (B.grading T) (ψ.sectionHom T)).ι)
    (q : W ⟶ (mapDomain (A.grading U) (B.grading U) (ψ.sectionHom U)).toScheme)
    (hqd : q ≫ mapHom (A.grading U) (B.grading U) (ψ.sectionHom U) = dk)
    (hqi : q ≫ (mapDomain (A.grading U) (B.grading U) (ψ.sectionHom U)).ι = ik) :
    twistMapAt (A.grading U) (A.grading T) (A.res h) n p hpd hpm ≫
        twistMapAt (A.grading T) (B.grading T) (ψ.sectionHom T) n w rfl rfl =
      twistMapAt (A.grading U) (B.grading U) (ψ.sectionHom U) n q hqd hqi ≫
        twistMapAt (B.grading U) (B.grading T) (B.res h) n j hjm hji := by
  have hd₁ : (w ≫ ((AlgebraicGeometry.Proj (B.grading T)).isoOfEq
          (mapDomain_sectionHom_comp_res ψ T U h hT hU)).inv) ≫
        mapHom (A.grading U) (B.grading T) ((ψ.sectionHom T).comp (A.res h)) = dk := by
    rw [Category.assoc, ← isoOfEq_comp_mapHom_comp_projInclusionMap ψ T U h hT hU,
      Iso.inv_hom_id_assoc]
    exact hwd
  have hi₁ : (w ≫ ((AlgebraicGeometry.Proj (B.grading T)).isoOfEq
          (mapDomain_sectionHom_comp_res ψ T U h hT hU)).inv) ≫
        (mapDomain (A.grading U) (B.grading T) ((ψ.sectionHom T).comp (A.res h))).ι =
      w ≫ (mapDomain (A.grading T) (B.grading T) (ψ.sectionHom T)).ι := by
    rw [Category.assoc, Scheme.isoOfEq_inv_ι]
  have hd₂ : (w ≫ ((AlgebraicGeometry.Proj (B.grading T)).isoOfEq
          (mapDomain_res_comp_sectionHom ψ T U h hT hU)).inv) ≫
        mapHom (A.grading U) (B.grading T) ((B.res h).comp (ψ.sectionHom U)) = dk := by
    rw [Category.assoc, ← isoOfEq_comp_chartDomainTrans_comp_mapHom ψ T U h hT hU,
      Iso.inv_hom_id_assoc, chartDomainTrans_comp_mapHom]
    exact hwd
  have hi₂ : (w ≫ ((AlgebraicGeometry.Proj (B.grading T)).isoOfEq
          (mapDomain_res_comp_sectionHom ψ T U h hT hU)).inv) ≫
        (mapDomain (A.grading U) (B.grading T) ((B.res h).comp (ψ.sectionHom U))).ι =
      w ≫ (mapDomain (A.grading T) (B.grading T) (ψ.sectionHom T)).ι := by
    rw [Category.assoc, Scheme.isoOfEq_inv_ι]
  rw [← twistMapAt_comp (A.grading U) (A.grading T) (B.grading T) (A.res h) (ψ.sectionHom T) n
      _ p w hd₁ hpd hpm rfl hi₁ rfl,
    ← twistMapAt_comp (A.grading U) (B.grading U) (B.grading T) (ψ.sectionHom U) (B.res h) n
      _ q j hd₂ hqd hqi hjm hi₂ hji]
  exact twistMapAt_congr (A.grading U) (B.grading T) (ψ.res_comp_sectionHom h).symm n _ _
    hd₁ hi₁ hd₂ hi₂

end NestedLeg

/-! ### The nested agreement of the affine-local comparison maps -/

section NestedAgree

attribute [local implicit_reducible] AlgebraicGeometry.Proj

/-- **A morphism between the pieces over a nested pair of affine opens of the base which commutes
with the two inclusions into `U(ψ)` is the inclusion of the pieces.** -/
public theorem eq_homOfLE_of_comp_pieceIncl (T U : S.affineOpens) (h : T.1 ≤ U.1)
    (k : (chartImage ψ T).toScheme ⟶ (chartImage ψ U).toScheme)
    (hk : k ≫ pieceIncl ψ U = pieceIncl ψ T) :
    k = (relativeProj B).scheme.homOfLE (chartImage_mono ψ h) := by
  rw [← cancel_mono (pieceIncl ψ U), hk, Scheme.homOfLE_homOfLE]

/-- **The inclusion of the piece over the smaller of a nested pair of affine opens of the base into
the piece over the larger, followed by the inclusion of the larger piece into `U(ψ)`, is the
inclusion of the smaller piece.** -/
public theorem homOfLE_comp_pieceIncl {T U : S.affineOpens} (h : T.1 ≤ U.1) :
    (relativeProj B).scheme.homOfLE (chartImage_mono ψ h) ≫ pieceIncl ψ U = pieceIncl ψ T :=
  Scheme.homOfLE_homOfLE _ _ _

/-- A leg out of the smaller piece through a chart domain, followed by a transition morphism, is the
inclusion of the pieces followed by the leg out of the larger piece, once the chart transition
satisfies the corresponding square. -/
private theorem leg_comp_eq_of_trans (T U : S.affineOpens) (h : T.1 ≤ U.1)
    (k : (chartImage ψ T).toScheme ⟶ (chartImage ψ U).toScheme)
    (hk : k ≫ pieceIncl ψ U = pieceIncl ψ T) {Z Z' : Scheme.{u}}
    (xT : (mapDomain (A.grading T.1) (B.grading T.1) (ψ.sectionHom T.1)).toScheme ⟶ Z)
    (xU : (mapDomain (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1)).toScheme ⟶ Z')
    (proj : Z ⟶ Z') (hx : chartDomainTrans ψ T.1 U.1 h T.2 U.2 ≫ xU = xT ≫ proj) :
    ((chartDomainIso ψ T).inv ≫ xT) ≫ proj = k ≫ (chartDomainIso ψ U).inv ≫ xU := by
  rw [eq_homOfLE_of_comp_pieceIncl ψ T U h k hk, ← cancel_epi (chartDomainIso ψ T).hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc, isoImage_hom_comp_homOfLE ψ h]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact hx.symm

/-- **The leg out of the smaller piece into `Proj Γ(T, A)`, followed by Tag 01NO's transition
morphism, is the inclusion of the pieces followed by the leg out of the larger piece.** -/
public theorem legSource_comp_projInclusionMap (T U : S.affineOpens) (h : T.1 ≤ U.1)
    (k : (chartImage ψ T).toScheme ⟶ (chartImage ψ U).toScheme)
    (hk : k ≫ pieceIncl ψ U = pieceIncl ψ T) :
    ((chartDomainIso ψ T).inv ≫
          mapHom (A.grading T.1) (B.grading T.1) (ψ.sectionHom T.1)) ≫
        projInclusionMap A T.1 U.1 h T.2 U.2 =
      k ≫ (chartDomainIso ψ U).inv ≫
        mapHom (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1) := by
  exact leg_comp_eq_of_trans ψ T U h k hk _ _ _ (chartDomainTrans_comp_mapHom ψ ..)

/-- **The companion of
`Stacks.AlgebraicGeometry.Tag07ZGTwist.legSource_comp_projInclusionMap` for the target algebra**:
the leg out of the smaller piece into `Proj Γ(T, B)`, followed by Tag 01NO's transition morphism,
is the inclusion of the pieces followed by the leg out of the larger piece. -/
public theorem legTarget_comp_projInclusionMap (T U : S.affineOpens) (h : T.1 ≤ U.1)
    (k : (chartImage ψ T).toScheme ⟶ (chartImage ψ U).toScheme)
    (hk : k ≫ pieceIncl ψ U = pieceIncl ψ T) :
    ((chartDomainIso ψ T).inv ≫
          (mapDomain (A.grading T.1) (B.grading T.1) (ψ.sectionHom T.1)).ι) ≫
        projInclusionMap B T.1 U.1 h T.2 U.2 =
      k ≫ (chartDomainIso ψ U).inv ≫
        (mapDomain (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1)).ι := by
  exact leg_comp_eq_of_trans ψ T U h k hk _ _ _ (chartDomainTrans_ι ψ ..)

/-- The morphism presenting the comparison map of the restriction `Γ(U, A) ⟶ Γ(T, A)` at the legs
out of the smaller piece, followed by the morphism of Tag 01MY for that restriction: it is the
inclusion of the pieces followed by the leg out of the larger piece. -/
public theorem presentSource_comp_mapHom (T U : S.affineOpens) (h : T.1 ≤ U.1)
    (k : (chartImage ψ T).toScheme ⟶ (chartImage ψ U).toScheme)
    (hk : k ≫ pieceIncl ψ U = pieceIncl ψ T) :
    (((chartDomainIso ψ T).inv ≫
            mapHom (A.grading T.1) (B.grading T.1) (ψ.sectionHom T.1)) ≫
          projInclusionTopSection A T.1 U.1 h T.2 U.2) ≫
        mapHom (A.grading U.1) (A.grading T.1) (A.res h) =
      k ≫ (chartDomainIso ψ U).inv ≫
        mapHom (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1) := by
  refine (Category.assoc _ _ _).trans ((comp_congr_right _
    (ProjInclusionTwist.projInclusionTopSection_comp_mapHom A T.1 U.1 h T.2 U.2)).trans ?_)
  exact legSource_comp_projInclusionMap ψ T U h k hk

/-- The same presenting morphism followed by the inclusion of the domain of definition of the
restriction: it is the leg out of the smaller piece. -/
public theorem presentSource_comp_ι (T U : S.affineOpens) (h : T.1 ≤ U.1) :
    (((chartDomainIso ψ T).inv ≫
            mapHom (A.grading T.1) (B.grading T.1) (ψ.sectionHom T.1)) ≫
          projInclusionTopSection A T.1 U.1 h T.2 U.2) ≫
        (mapDomain (A.grading U.1) (A.grading T.1) (A.res h)).ι =
      (chartDomainIso ψ T).inv ≫
        mapHom (A.grading T.1) (B.grading T.1) (ψ.sectionHom T.1) :=
  (Category.assoc _ _ _).trans
    ((comp_congr_right _ (projInclusionTopSection_ι A T.1 U.1 h T.2 U.2)).trans
      (Category.comp_id _))

/-- The companion of `Stacks.AlgebraicGeometry.Tag07ZGTwist.presentSource_comp_mapHom` for the
target algebra. -/
public theorem presentTarget_comp_mapHom (T U : S.affineOpens) (h : T.1 ≤ U.1)
    (k : (chartImage ψ T).toScheme ⟶ (chartImage ψ U).toScheme)
    (hk : k ≫ pieceIncl ψ U = pieceIncl ψ T) :
    (((chartDomainIso ψ T).inv ≫
            (mapDomain (A.grading T.1) (B.grading T.1) (ψ.sectionHom T.1)).ι) ≫
          projInclusionTopSection B T.1 U.1 h T.2 U.2) ≫
        mapHom (B.grading U.1) (B.grading T.1) (B.res h) =
      k ≫ (chartDomainIso ψ U).inv ≫
        (mapDomain (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1)).ι := by
  refine (Category.assoc _ _ _).trans ((comp_congr_right _
    (ProjInclusionTwist.projInclusionTopSection_comp_mapHom B T.1 U.1 h T.2 U.2)).trans ?_)
  exact legTarget_comp_projInclusionMap ψ T U h k hk

/-- The companion of `Stacks.AlgebraicGeometry.Tag07ZGTwist.presentSource_comp_ι` for the target
algebra. -/
public theorem presentTarget_comp_ι (T U : S.affineOpens) (h : T.1 ≤ U.1) :
    (((chartDomainIso ψ T).inv ≫
            (mapDomain (A.grading T.1) (B.grading T.1) (ψ.sectionHom T.1)).ι) ≫
          projInclusionTopSection B T.1 U.1 h T.2 U.2) ≫
        (mapDomain (B.grading U.1) (B.grading T.1) (B.res h)).ι =
      (chartDomainIso ψ T).inv ≫
        (mapDomain (A.grading T.1) (B.grading T.1) (ψ.sectionHom T.1)).ι :=
  (Category.assoc _ _ _).trans
    ((comp_congr_right _ (projInclusionTopSection_ι B T.1 U.1 h T.2 U.2)).trans
      (Category.comp_id _))

/-- **The affine-local comparison maps on the `n`-th twist agree on a nested overlap.** For affine
opens `T ⊆ U` of the base, the affine-local comparison map over `U`, pulled back along the
inclusion of the piece over `T` into the piece over `U`, is the affine-local comparison map over
`T`. -/
public theorem relativeTwistChart_nested (n : ℤ) (T U : S.affineOpens) (h : T.1 ≤ U.1)
    (k : (chartImage ψ T).toScheme ⟶ (chartImage ψ U).toScheme)
    (hk : k ≫ pieceIncl ψ U = pieceIncl ψ T) :
    (Scheme.Modules.pullbackCongr hk).inv.app
          ((Scheme.Modules.pullback (relativeMapHom ψ)).obj (relativeTwist A n)) ≫
        (Scheme.Modules.pullbackComp k (pieceIncl ψ U)).inv.app
          ((Scheme.Modules.pullback (relativeMapHom ψ)).obj (relativeTwist A n)) ≫
        (Scheme.Modules.pullback k).map (relativeTwistChart ψ n U) ≫
        (Scheme.Modules.pullbackComp k (pieceIncl ψ U)).hom.app
          ((Scheme.Modules.pullback ψ.relativeMapDomain.ι).obj (relativeTwist B n)) ≫
        (Scheme.Modules.pullbackCongr hk).hom.app
          ((Scheme.Modules.pullback ψ.relativeMapDomain.ι).obj (relativeTwist B n)) =
      relativeTwistChart ψ n T := by
  have hcAU := (Category.assoc _ _ _).trans (pieceIncl_comp_relativeMapHom ψ U).symm
  have hcAT := (Category.assoc _ _ _).trans (pieceIncl_comp_relativeMapHom ψ T).symm
  have hcBU := (Category.assoc _ _ _).trans (pieceIncl_comp_ι ψ U).symm
  have hcBT := (Category.assoc _ _ _).trans (pieceIncl_comp_ι ψ T).symm
  have hkcA : k ≫ pieceIncl ψ U ≫ relativeMapHom ψ = pieceIncl ψ T ≫ relativeMapHom ψ :=
    (Category.assoc _ _ _).symm.trans (congrArg (fun z => z ≫ relativeMapHom ψ) hk)
  have hkcB : k ≫ pieceIncl ψ U ≫ ψ.relativeMapDomain.ι =
      pieceIncl ψ T ≫ ψ.relativeMapDomain.ι :=
    (Category.assoc _ _ _).symm.trans (congrArg (fun z => z ≫ ψ.relativeMapDomain.ι) hk)
  have hsrc := (comp_congr_right
      ((Scheme.Modules.pullbackComp (pieceIncl ψ T) (relativeMapHom ψ)).hom.app
        (relativeTwist A n))
      (chartTwistIso_hom_nested A n T U h k hcAU hcAT hkcA
        (((chartDomainIso ψ T).inv ≫
            mapHom (A.grading T.1) (B.grading T.1) (ψ.sectionHom T.1)) ≫
          projInclusionTopSection A T.1 U.1 h T.2 U.2) rfl
        (presentSource_comp_mapHom ψ T U h k hk) (presentSource_comp_ι ψ T U h))).trans
    (prefix_nested_rearrange k (pieceIncl ψ U) (relativeMapHom ψ) hk hkcA
      (relativeTwist A n) _ _)
  have htgt := (comp_congr_right
      ((Scheme.Modules.pullbackComp (pieceIncl ψ T) ψ.relativeMapDomain.ι).hom.app
        (relativeTwist B n))
      (chartTwistIso_hom_nested B n T U h k hcBU hcBT hkcB
        (((chartDomainIso ψ T).inv ≫
            (mapDomain (A.grading T.1) (B.grading T.1) (ψ.sectionHom T.1)).ι) ≫
          projInclusionTopSection B T.1 U.1 h T.2 U.2) rfl
        (presentTarget_comp_mapHom ψ T U h k hk) (presentTarget_comp_ι ψ T U h))).trans
    (prefix_nested_rearrange k (pieceIncl ψ U) ψ.relativeMapDomain.ι hk hkcB
      (relativeTwist B n) _ _)
  have hsplice := splice_of_comp
    (twistMapAt_comp_leg_refl (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1) n k
      (chartDomainIso ψ U).inv)
    (twistMapAt_nested_leg ψ T.1 U.1 h T.2 U.2 n (chartDomainIso ψ T).inv
      ((Category.assoc _ _ _).symm.trans (legSource_comp_projInclusionMap ψ T U h k hk))
      (((chartDomainIso ψ T).inv ≫
          mapHom (A.grading T.1) (B.grading T.1) (ψ.sectionHom T.1)) ≫
        projInclusionTopSection A T.1 U.1 h T.2 U.2)
      (presentSource_comp_mapHom ψ T U h k hk) (presentSource_comp_ι ψ T U h)
      (((chartDomainIso ψ T).inv ≫
          (mapDomain (A.grading T.1) (B.grading T.1) (ψ.sectionHom T.1)).ι) ≫
        projInclusionTopSection B T.1 U.1 h T.2 U.2)
      (presentTarget_comp_mapHom ψ T U h k hk) (presentTarget_comp_ι ψ T U h)
      (k ≫ (chartDomainIso ψ U).inv) (Category.assoc _ _ _) (Category.assoc _ _ _))
  exact nested_of_comp_target k hk
    (comp_eq_id_of_hom_eq (chartTargetIso ψ n T) _ _ (chartTargetIso_hom_eq ψ n T hcBT))
    (relativeTwistChart_comp_target ψ n U hcAU hcBU)
    (relativeTwistChart_comp_target ψ n T hcAT hcBT) hsrc htgt hsplice

end NestedAgree

end Stacks.AlgebraicGeometry.Tag07ZGTwist

end
