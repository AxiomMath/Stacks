module

public import
  StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.NewShriekComparisonRestrict
public import
  StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.NewShriekComparisonPlusIso
public import
  StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.OpenImmersionPrecomposition
public import
  StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.NewShriekAffineChartsNormalization
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.NormalizedExistence
public import
  StacksFrontier.AlgebraicGeometry.Duality.CompactlySupportedCohomology.LowerShriekAdjunction
public import StacksFrontier.AlgebraicGeometry.Duality.NewShriekTwistComparison
public meta import StacksFrontier.Tactic.HEqCongr

/-!
# `f_new^!` does not depend on the dualizing complex of the base

In Situation [Stacks, Tag 0AU4], let `ω_S^•` and `ω_S'^•` be two dualizing complexes on `S`, let
`p : X ⟶ S` be of finite type and let `ω_X^•` be normalized relative to `ω_S^•`. Then

`p_new^! ω_S'^• = R𝓗om(Lp^* R𝓗om(ω_S'^•, ω_S^•), ω_X^•)`

is normalized relative to `ω_S'^•`; hence it is the complex normalized relative to `ω_S'^•`. On an
open `W ⊆ X` separated over `S` the normalization is the composite

`(p_new^! ω_S'^•)|_W ≅ (W → S)_new^! ω_S'^• ≅ (W → S)^! ω_S'^•`

of the restriction of `p_new^!` to `W` and of the duality formula of [Stacks, Tag 0AU2] for the
separated morphism `W → S`, formed with the identification `ω_X^•|_W ≅ (W → S)^! ω_S^•`. These
are compatible with restriction because the duality formula restricts to opens
(`Stacks.Duality.NormalizedOnOpens.upperShriekStdIsoFNewShriekOfIso_restrict`) and does not depend
on the compactification (`upperShriekStdIsoFNewShriekOfIso_upperShriekPlusIso`).

This is the step of [Stacks, Tag 0BV3] which in the source is the citation of
[Stacks, Tag 0A9T]: there the comparison is made for `ω_S'^• = ω_S^• ⊗ ℒ`, here directly for
`ω_S'^•`. By the uniqueness of normalized complexes ([Stacks, Tag 0AU7]) it gives, for
`f : X ⟶ Y` over `S`, `ω_X'^• ≅ f_new^! ω_Y'^•` with `f_new^!` formed from `ω_X^•`, `ω_Y^•`, and
then `Stacks.Duality.fNewShriekStdIsoOfIso` gives [Stacks, Tag 0BV3] itself.

## Main definitions

* `Stacks.Duality.NormalizedOnOpens.toStd` — `D^+_QCoh(𝒪_Z)` at the locally small model, read at
  the standard model.
* `Stacks.Duality.NormalizedOnOpens.shriekStdIso` — `j^! ≅ Lj^*` for an open immersion `j`, read
  at the standard model.
* `Stacks.Duality.NormalizedOnOpens.twistNormalized` — `p_new^! ω_S'^•` with its normalizations
  relative to `ω_S'^•`.
* `Stacks.Duality.NormalizedOnOpens.stdComplexIsoTwist` — `ω_X'^• ≅ p_new^! ω_S'^•`.
* `Stacks.Duality.NormalizedOnOpens.stdComplexIsoFNewShriek` — `ω_X'^• ≅ f_new^! ω_Y'^•`.

## Main results

* `Stacks.Duality.NormalizedOnOpens.fNewShriekIndependenceIso` — **[Stacks, Tag 0BV3]**.

## Implementation notes

The compactifications computing the upper shriek functors are the parameter `c` of
`Stacks.Duality.UpperShriek.ofCompactifications`, the formalism in which normalized complexes are
defined in this repository; the statement holds for every such choice. The two worlds of objects
— schemes of `FTS_S` and opens of `X` — are bridged by the `heq_congr` tactic, which leaves the
definitional checks between them to the kernel.

## References

* [Stacks Project, Tag 0BV3](https://stacks.math.columbia.edu/tag/0BV3)
* [Stacks Project, Tag 0AU2](https://stacks.math.columbia.edu/tag/0AU2)
* [Stacks Project, Tag 0AU7](https://stacks.math.columbia.edu/tag/0AU7)
* [Stacks Project, Tag 0A9T](https://stacks.math.columbia.edu/tag/0A9T)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace Stacks.Duality.NormalizedOnOpens

open Stacks.Duality.TwistedInverseImageDuality Stacks.Duality.UpperShriekDuality
open CategoryTheory.MonoidalClosed (dualInto)

attribute [local instance] stdMonoidal stdSymmetric stdMonoidalClosed

variable (c : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), IsShriekable f → CompactificationOf (Over.mk f))

/-! ### Chases in an abstract category -/

section Chase

variable {𝒞 : Type*} [Category 𝒞]

/-- Inverting both sides of `u ≫ v = x ≫ y` for isomorphisms. -/
theorem inv_comp_inv_eq_of_hom_comp_eq {a b c d : 𝒞} (u : a ≅ b) (v : b ≅ d) (x : a ≅ c)
    (y : c ≅ d) (h : u.hom ≫ v.hom = x.hom ≫ y.hom) : v.inv ≫ u.inv = y.inv ≫ x.inv := by
  have := congrArg Iso.inv (Iso.ext h : u ≪≫ v = x ≪≫ y)
  simpa using this

/-- Moving the isomorphisms of `u ≫ v = x ≫ y` across. -/
theorem inv_comp_hom_eq_of_hom_comp_eq {a b c d : 𝒞} (u : a ≅ b) (v : b ≅ d) (x : a ≅ c)
    (y : c ≅ d) (h : u.hom ≫ v.hom = x.hom ≫ y.hom) : u.inv ≫ x.hom = v.hom ≫ y.inv := by
  rw [Iso.inv_comp_eq, reassoc_of% h, Iso.hom_inv_id, Category.comp_id]

/-- The chase behind `shriekStdIso_factorIso`. -/
theorem shriekStdIso_factorIso_chase {𝒟 : Type*} [Category 𝒟] (L : 𝒟 ⥤ 𝒞)
    {a0 a1 a2 a4 a5 a6 : 𝒞} {b0 b1 b2 : 𝒟} (a : a0 ⟶ a1) (b : a1 ⟶ a2) (m : a2 ⟶ L.obj b0)
    (s : b0 ⟶ b1) (t : b1 ⟶ b2) (k1 : a0 ⟶ a4) (pk : a4 ⟶ a5) (π : L.obj b2 ≅ a5)
    (n : a2 ⟶ a6) (m' : a6 ⟶ L.obj b1) (q : a6 ⟶ a4)
    (F : k1 = a ≫ b ≫ n ≫ q) (N : n ≫ m' = m ≫ L.map s) (P : m' ≫ L.map t ≫ π.hom = q ≫ pk) :
    a ≫ (b ≫ m) ≫ L.map (s ≫ t) = (k1 ≫ pk) ≫ π.inv := by
  rw [F, ← cancel_mono π.hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Functor.map_comp]
  rw [← P, reassoc_of% N]

/-- The chase behind `upperShriekStdIsoFNewShriekOfIso_trans`. -/
theorem upperShriekStdIsoFNewShriekOfIso_trans_chase {o0 o1 o2 o3 o4 o5 o6 o7 : 𝒞}
    (ψ : o0 ⟶ o1) (me : o1 ⟶ o2) (ms : o2 ⟶ o3) (mes : o1 ⟶ o3) (i' : o3 ⟶ o4)
    (d' : o4 ⟶ o5) (i : o2 ⟶ o6) (d : o6 ⟶ o7) (t : o7 ⟶ o5) (t0 : o6 ⟶ o4)
    (hm : mes = me ≫ ms) (hi : i ≫ t0 = ms ≫ i') (Nat : d ≫ t = t0 ≫ d') :
    ψ ≫ mes ≫ i' ≫ d' = (ψ ≫ me ≫ i ≫ d) ≫ t := by
  rw [hm]
  simp only [Category.assoc]
  rw [Nat, reassoc_of% hi]

/-- Mapping `a ≫ b = x ≫ y` and pasting `G y ≫ m = r`. -/
theorem map_comp_paste_chase {𝒟 : Type*} [Category 𝒟] (G : 𝒟 ⥤ 𝒞) {d0 d1 d2 d3 : 𝒟} {o : 𝒞}
    (a : d0 ⟶ d1) (b : d1 ⟶ d2) (x : d0 ⟶ d3) (y : d3 ⟶ d2) (m : G.obj d2 ⟶ o)
    (r : G.obj d3 ⟶ o) (F : a ≫ b = x ≫ y) (E : G.map y ≫ m = r) :
    G.map a ≫ G.map b ≫ m = G.map x ≫ r := by
  rw [← E, ← G.map_comp_assoc, F, G.map_comp_assoc]

/-- The chase behind `upperShriekPrecompOpenIso_std`. -/
theorem upperShriekPrecompOpenIso_std_chase {𝒟 : Type*} [Category 𝒟] (L : 𝒟 ⥤ 𝒞)
    {a b c : 𝒞} {e f : 𝒟} (w : a ≅ b) (mh : a ⟶ L.obj e) (s1 : e ≅ f) (π : L.obj f ≅ c)
    (s2 : b ≅ c) (R : L.obj e ≅ b) (hR : R.hom = L.map s1.hom ≫ π.hom ≫ s2.inv)
    (P : mh ≫ L.map s1.hom ≫ π.hom = w.hom ≫ s2.hom) : w.inv ≫ mh = R.inv := by
  rw [Iso.inv_comp_eq, ← cancel_mono R.hom, Category.assoc, Iso.inv_hom_id, Category.comp_id, hR,
    reassoc_of% P, Iso.hom_inv_id, Category.comp_id]

/-- Moving two isomorphisms of `u ≫ v = x ≫ y` across. -/
theorem inv_comp_eq_comp_inv_of_hom_comp_eq {a b c d : 𝒞} (u : a ≅ b) {v : b ⟶ d} {x : a ⟶ c}
    (y : c ≅ d) (h : u.hom ≫ v = x ≫ y.hom) : u.inv ≫ x = v ≫ y.inv := by
  rw [Iso.inv_comp_eq, reassoc_of% h, Iso.hom_inv_id, Category.comp_id]

/-- Moving the components of two natural isomorphisms across, one of them under a functor. -/
theorem map_inv_app_comp_eq_comp_inv_app {𝒜 ℬ : Type*} [Category 𝒜] [Category ℬ]
    {F G : 𝒜 ⥤ ℬ} {F' G' : 𝒜 ⥤ 𝒞} (L : ℬ ⥤ 𝒞) (α : F ≅ G) (β : F' ≅ G') (M : 𝒜)
    {v : L.obj (G.obj M) ⟶ G'.obj M} {x : L.obj (F.obj M) ⟶ F'.obj M}
    (h : L.map (α.hom.app M) ≫ v = x ≫ β.hom.app M) :
    L.map (α.inv.app M) ≫ x = v ≫ β.inv.app M := by
  rw [← cancel_epi (L.map (α.hom.app M)), ← L.map_comp_assoc, Iso.hom_inv_id_app, L.map_id,
    Category.id_comp, reassoc_of% h, Iso.hom_inv_id_app, Category.comp_id]

/-- Inverting `u ≫ v = w` for isomorphisms. -/
theorem inv_comp_inv_eq_inv_of_hom_comp_eq {a b c : 𝒞} (u : a ≅ b) (v : b ≅ c) (w : a ≅ c)
    (h : u.hom ≫ v.hom = w.hom) : v.inv ≫ u.inv = w.inv := by
  have := congrArg Iso.inv (Iso.ext h : u ≪≫ v = w)
  simpa using this

/-- Inverting `u = x ≫ y` for isomorphisms. -/
theorem inv_eq_inv_comp_inv_of_hom_eq_comp {a b c : 𝒞} (u : a ≅ c) (x : a ≅ b) (y : b ≅ c)
    (h : u.hom = x.hom ≫ y.hom) : u.inv = y.inv ≫ x.inv :=
  (inv_comp_inv_eq_inv_of_hom_comp_eq x y u h.symm).symm

/-- Cancelling `a = 𝟙` and `L f = 𝟙` in `a ≫ b ≫ c = d ≫ e ≫ L f`. -/
theorem comp_eq_comp_of_id_chase {𝒟 : Type*} [Category 𝒟] (L : 𝒟 ⥤ 𝒞) {o0 o1 o2 : 𝒞}
    {d0 : 𝒟} (a : o0 ⟶ o0) (b : o0 ⟶ o1) (c : o1 ⟶ L.obj d0) (d : o0 ⟶ o2)
    (e : o2 ⟶ L.obj d0) (f : d0 ⟶ d0) (F : a ≫ b ≫ c = d ≫ e ≫ L.map f) (ha : a = 𝟙 _)
    (hf : f = 𝟙 _) : b ≫ c = d ≫ e := by
  rw [ha, hf, L.map_id, Category.id_comp, Category.comp_id] at F
  exact F

/-- The chase behind `restrictNewShriekIso_restrict`. -/
theorem restrictNewShriekIso_restrict_chase {𝒟 : Type*} [Category 𝒟] (L : 𝒟 ⥤ 𝒞)
    {x0 z1 z2 w1 v1 v2 u : 𝒞} {y0 y1 y2 : 𝒟} (p : x0 ⟶ L.obj y0) (r : y0 ⟶ y1)
    (o : y1 ⟶ y2) (si : L.obj y2 ⟶ z1) (fi : z1 ⟶ z2) (sr : L.obj y2 ⟶ w1) (ci : w1 ⟶ z2)
    (nr : L.obj y1 ⟶ v1) (opi : v1 ⟶ w1) (eq : v1 ⟶ v2) (oei : v2 ⟶ z2) (nr' : L.obj y1 ⟶ v2)
    (di : v2 ⟶ u) (ow' : u ⟶ z2) (r' : x0 ⟶ u) (dp : u ⟶ v2)
    (A : si ≫ fi = sr ≫ ci) (B : L.map o ≫ sr = nr ≫ opi) (C : opi ≫ ci = eq ≫ oei)
    (G : r' ≫ dp = p ≫ L.map r ≫ nr') (hdi : dp ≫ di = 𝟙 u) (F : nr ≫ eq = nr')
    (D : oei = di ≫ ow') :
    p ≫ L.map (r ≫ o) ≫ si ≫ fi = r' ≫ ow' := by
  rw [L.map_comp]
  simp only [Category.assoc]
  rw [A, reassoc_of% B, C, reassoc_of% F, D, ← reassoc_of% G, reassoc_of% hdi]

/-- The chase behind `normalizationPullIso_restrict`. -/
theorem normalizationPullIso_restrict_chase {𝒟 : Type*} [Category 𝒟] (L : 𝒟 ⥤ 𝒞)
    {x0 x1 x2 x3 z0 z1 z2 w0 : 𝒞} {y0 y2 y3 : 𝒟}
    (ca' : x0 ⟶ x2) (csW' : x0 ⟶ x1) (aW'i : x1 ⟶ x2) (sW' : x2 ⟶ x3) (pci : x3 ⟶ L.obj y3)
    (fs : x1 ⟶ z1) (ha : z1 ⟶ z2) (fxi : z2 ⟶ x2) (fx : x2 ⟶ z2)
    (shK : z2 ⟶ L.obj y2) (sWK : y2 ⟶ y3) (fsK : x0 ⟶ z0) (shcs : z0 ⟶ z1) (shc : z0 ⟶ z2)
    (shK0 : z0 ⟶ L.obj y0) (cwa : y0 ⟶ y2) (cg : x0 ⟶ w0)
    (sri : w0 ⟶ L.obj y0) (dri : w0 ⟶ L.obj y0) (hca' : ca' = csW' ≫ aW'i)
    (Hα : aW'i = fs ≫ ha ≫ fxi) (P1 : fx ≫ shK ≫ L.map sWK = sW' ≫ pci) (hfx : fxi ≫ fx = 𝟙 _)
    (natfS : csW' ≫ fs = fsK ≫ shcs) (hsh : shc = shcs ≫ ha) (natSh : shc ≫ shK = shK0 ≫ L.map cwa)
    (P3 : fsK ≫ shK0 = cg ≫ sri) (hDR : dri = sri) :
    cg ≫ dri ≫ L.map (cwa ≫ sWK) = (ca' ≫ sW') ≫ pci := by
  rw [hDR, hca', Hα]
  simp only [Category.assoc]
  rw [← P1, reassoc_of% hfx, reassoc_of% natfS, ← Category.assoc shcs ha, ← hsh,
    reassoc_of% natSh, ← reassoc_of% P3, L.map_comp]

/-- The chase behind the compatibility of `twistLocalIso` with restriction. -/
theorem twistLocalIso_compat_chase {𝒟 : Type*} [Category 𝒟] (L : 𝒟 ⥤ 𝒞)
    {a0 a1 a2 a3 c1 c2 d1 d2 : 𝒞} {b1 b2 b3 b4 b5 : 𝒟}
    (fx : a0 ⟶ a1) (shφ : a1 ⟶ a2) (fsi : a2 ⟶ a3) (sh1 : a1 ⟶ L.obj b1) (sh2 : a2 ⟶ L.obj b4)
    (shi2 : L.obj b4 ⟶ a2) (φs : b1 ⟶ b4) (sW : b1 ⟶ b2) (ut : b2 ⟶ b3) (rn : b3 ⟶ b5)
    (cs : b5 ⟶ b4) (s' : a0 ⟶ c1) (pci : c1 ⟶ L.obj b2) (ut' : c1 ⟶ c2) (pci' : c2 ⟶ L.obj b3)
    (shiM : L.obj b5 ⟶ d1) (fsiM : d1 ⟶ d2) (rn' : c2 ⟶ d2) (shcs : d1 ⟶ a2) (cs' : d2 ⟶ a3)
    (N1 : shφ ≫ sh2 = sh1 ≫ L.map φs) (hφ : φs = sW ≫ ut ≫ rn ≫ cs)
    (P1 : fx ≫ sh1 ≫ L.map sW = s' ≫ pci) (Nu : pci ≫ L.map ut = ut' ≫ pci')
    (C : pci' ≫ L.map rn ≫ shiM ≫ fsiM = rn') (Nc1 : L.map cs ≫ shi2 = shiM ≫ shcs)
    (Nc2 : shcs ≫ fsi = fsiM ≫ cs') (hsh : sh2 ≫ shi2 = 𝟙 _) :
    fx ≫ shφ ≫ fsi = s' ≫ ut' ≫ rn' ≫ cs' := by
  have e1 : shφ = sh1 ≫ L.map φs ≫ shi2 := by
    rw [← reassoc_of% N1, hsh, Category.comp_id]
  rw [e1, hφ, ← C]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% Nc1, Nc2, reassoc_of% P1, reassoc_of% Nu]

end Chase

/-! ### Reading `D^+_QCoh` at the standard model -/

/-- `D^+_QCoh(𝒪_Z)` at the locally small model, read at the standard model. -/
abbrev toStd (Z : Scheme.{u}) : quasiCoherentDerivedCategoryPlusOfModel Z ⥤ Std Z :=
  ObjectProperty.ι _ ⋙ ObjectProperty.ι _ ⋙ (comparison Z).inverse

/-- **`j^! ≅ Lj^*` at the standard model**, for a shriekable open immersion `j`
([Stacks, Tag 0AU0]). -/
def shriekStdIso {U Z : Scheme.{u}} (j : U ⟶ Z) (hj : IsShriekable j) [IsOpenImmersion j] :
    UpperShriek.shriekOf c j hj ⋙ toStd U ≅ toStd Z ⋙ pull j :=
  Functor.isoWhiskerRight (UpperShriek.shriekOfIsoPullbackOfIsOpenImmersion c j hj)
      (ObjectProperty.ι _ ⋙ (comparison U).inverse) ≪≫
    Functor.isoWhiskerLeft (ObjectProperty.ι _ ⋙ ObjectProperty.ι _) (pullModelConj j)

/-- The component of `shriekStdIso` at `E` is the comparison image of the component of
`UpperShriek.shriekOfIsoPullbackOfIsOpenImmersion` followed by that of `pullModelConj j`. -/
theorem shriekStdIso_hom_app {U Z : Scheme.{u}} (j : U ⟶ Z) (hj : IsShriekable j)
    [IsOpenImmersion j] (E : quasiCoherentDerivedCategoryPlusOfModel Z) :
    (shriekStdIso c j hj).hom.app E =
      (comparison U).inverse.map
          ((UpperShriek.shriekOfIsoPullbackOfIsOpenImmersion c j hj).hom.app E).hom ≫
        (pullModelConj j).hom.app E.obj.obj :=
  rfl

/-- **`j^! ≅ Lj^*` is compatible with composition** at the standard model: for shriekable open
immersions `h`, `j` with `h ≫ j = k`, the comparison `k^! ≅ h^! ∘ j^!` corresponds to
`Lk^* ≅ Lh^* ∘ Lj^*`. -/
theorem shriekStdIso_factorIso {W U Z : Scheme.{u}} {h : W ⟶ U} {j : U ⟶ Z} {k : W ⟶ Z}
    (e : h ≫ j = k) (hh : IsShriekable h) (hj : IsShriekable j) (hk : IsShriekable k)
    [IsOpenImmersion h] [IsOpenImmersion j] [IsOpenImmersion k]
    (E : quasiCoherentDerivedCategoryPlusOfModel Z) :
    (toStd W).map ((UpperShriek.factorIsoOf c e hh hj hk).hom.app E) ≫
        (shriekStdIso c h hh).hom.app ((UpperShriek.shriekOf c j hj).obj E) ≫
        (pull h).map ((shriekStdIso c j hj).hom.app E) =
      (shriekStdIso c k hk).hom.app E ≫ (pullCompIso h j k e).inv.app ((toStd Z).obj E) := by
  have F : (comparison W).inverse.map
      ((UpperShriek.shriekOfIsoPullbackOfIsOpenImmersion c k hk).hom.app E).hom =
      (comparison W).inverse.map ((UpperShriek.factorIsoOf c e hh hj hk).hom.app E).hom.hom ≫
        (comparison W).inverse.map
          ((UpperShriek.shriekOfIsoPullbackOfIsOpenImmersion c h hh).hom.app
            ((UpperShriek.shriekOf c j hj).obj E)).hom ≫
        (comparison W).inverse.map ((Stacks.Duality.derivedPullback h).map
          ((UpperShriek.shriekOfIsoPullbackOfIsOpenImmersion c j hj).hom.app E).hom) ≫
        (comparison W).inverse.map ((Stacks.Duality.derivedPullbackCompIso h j).hom.app E.obj.obj ≫
          eqToHom (congrArg (fun t => (Stacks.Duality.derivedPullback t).obj E.obj.obj) e)) := by
    rw [UpperShriek.shriekOfIsoPullbackOfIsOpenImmersion_factorIso c e hh hj hk E]
    simp only [ObjectProperty.FullSubcategory.comp_hom, Functor.map_comp,
      quasiCoherentDerivedPullback_map_hom, quasiCoherentDerivedPullbackCompIso_hom_app_hom,
      quasiCoherentDerivedPullbackCongr_hom_app_hom]
  have N : (comparison W).inverse.map ((Stacks.Duality.derivedPullback h).map
        ((UpperShriek.shriekOfIsoPullbackOfIsOpenImmersion c j hj).hom.app E).hom) ≫
        (pullModelConj h).hom.app ((Stacks.Duality.derivedPullback j).obj E.obj.obj) =
      (pullModelConj h).hom.app ((UpperShriek.shriekOf c j hj).obj E).obj.obj ≫
        (pull h).map ((comparison U).inverse.map
          ((UpperShriek.shriekOfIsoPullbackOfIsOpenImmersion c j hj).hom.app E).hom) :=
    (pullModelConj h).hom.naturality _
  have P := pullModelConj_hom_app_comp_pullCompIso h j k e E.obj.obj
  rw [shriekStdIso_hom_app, shriekStdIso_hom_app, shriekStdIso_hom_app]
  exact shriekStdIso_factorIso_chase (pull h) _ _ _ _ _ _ _ ((pullCompIso h j k e).app _) _ _ _
    F N P

/-! ### Objects of `D^+_Coh` on the base -/

section Base

/-- A dualizing complex on a Noetherian scheme lies in `D^+_Coh`. -/
theorem plusCoh_of_isDualizing {S : Scheme.{u}} [IsNoetherian S] {K : Std S}
    (hK : IsDualizing K) : plusCoh S K :=
  ⟨isBoundedBelow_of_isDualizing_std hK, (coherentDuality_spec S hK).1⟩

/-- The standard form of a dualizing complex at the locally small model is dualizing. -/
theorem isDualizing_toStd {S : Scheme.{u}} [IsLocallyNoetherian S]
    {N : quasiCoherentDerivedCategoryPlusOfModel S} (h : IsDualizingComplex N.obj.obj) :
    IsDualizing ((toStd S).obj N) :=
  isDualizingComplex_standard_of_isDualizingComplex h

variable {S : Scheme.{u}} [IsNoetherian S]

/-- An object of `D^+_Coh(𝒪_S)` at the standard model, as an object of `D^+_QCoh(𝒪_S)` at the
locally small model. -/
abbrev plusOfStd (M : (plusCoh S).FullSubcategory) : quasiCoherentDerivedCategoryPlusOfModel S :=
  ⟨toQCoh ⟨M.obj, plusCoh_le_qcoh _ M.property⟩, ((plusCoh_iff M.obj).1 M.property).1⟩

/-- An object of `D^+_QCoh(𝒪_S)` whose standard form is in `D^+_Coh` is recovered from it. -/
def plusOfStdIso (N : quasiCoherentDerivedCategoryPlusOfModel S)
    (hN : plusCoh S ((toStd S).obj N)) : plusOfStd ⟨(toStd S).obj N, hN⟩ ≅ N :=
  ObjectProperty.isoMk _ (ObjectProperty.isoMk _ ((comparison S).counitIso.app N.obj.obj))

end Base

/-! ### The normalizations at the standard model -/

section Normalization

variable {X S : Scheme.{u}} [IsNoetherian S] {p : X ⟶ S} {hp : IsFiniteTypeOverNoetherian p}
  {ωS : quasiCoherentDerivedCategoryPlusOfModel S}
  (𝒦X : NormalizedOnOpens (UpperShriek.ofCompactifications c) hp ωS)
  (hK : IsDualizing ((toStd S).obj ωS))

/-- The normalization `ω_X^•|_W ≅ (W → S)^! ω_S^•` of an open `W ⊆ X` separated over `S`, read at
the standard model as `(W → S)^! K ≅ Lι_W^* ω_X^•`. -/
def normalizationPullIso (W : X.Opens) (hW : IsShriekable (W.ι ≫ p)) :
    upperShriekDualizing (ftsHomSelf hW) (c _ hW) hK ≅ (pull W.ι).obj (stdComplex c 𝒦X) :=
  (toStd W.toScheme).mapIso
      ((UpperShriek.shriekOf c (W.ι ≫ p) hW).mapIso
          (plusOfStdIso ωS (plusCoh_of_isDualizing hK)) ≪≫
        (𝒦X.localIso W hW).symm) ≪≫
    (shriekStdIso c W.ι (hp.isShriekable_ι W)).app 𝒦X.complex

/-- **The comparison on an open `W ⊆ X` separated over `S`**: for `M ∈ D^+_Coh(𝒪_S)`,
`(p_new^! M)|_W ≅ (W → S)_new^! M ≅ (W → S)^! M`, the first by restriction of `p_new^!` and the
second by [Stacks, Tag 0AU2] formed with `normalizationPullIso`. -/
def restrictNewShriekIso (W : X.Opens) (hW : IsShriekable (W.ι ≫ p))
    (M : (plusCoh S).FullSubcategory) :
    (pull W.ι).obj ((fNewShriekStd p (stdComplex c 𝒦X) ((toStd S).obj ωS)).obj M.obj) ≅
      (toStd W.toScheme).obj ((UpperShriek.shriekOf c (W.ι ≫ p) hW).obj (plusOfStd M)) :=
  (@fNewShriekRestrictIso (ftsOf (W.ι ≫ p) hW.separatedFiniteType).left X
      (ftsOf (𝟙 S) (isSeparatedFiniteType_id S)).left W.ι (inferInstanceAs (IsOpenImmersion W.ι)) p
      (ftsHomSelf hW).left rfl (stdComplex c 𝒦X) ((toStd S).obj ωS)).app
        ((plusCoh (ftsOf (𝟙 S) (isSeparatedFiniteType_id S)).left).ι.obj M) ≪≫
    ((upperShriekStdIsoFNewShriekOfIso (ftsHomSelf hW) (c _ hW) hK
      (normalizationPullIso c 𝒦X hK W hW)).app M).symm

end Normalization

/-! ### Auxiliary identities -/

section Aux

/-- The duality formula of [Stacks, Tag 0AU2] through a composite identification `e ≪≫ s`. -/
theorem upperShriekStdIsoFNewShriekOfIso_trans {T : Scheme.{u}} [IsNoetherian T] {A B : FTS T}
    (g : A ⟶ B) (j : CompactificationOf (Over.mk g.left)) {K : Std B.left} (hK : IsDualizing K)
    {ω ω' : Std A.left} (e : upperShriekDualizing g j hK ≅ ω) (s : ω ≅ ω')
    (M : (plusCoh B.left).FullSubcategory) :
    (upperShriekStdIsoFNewShriekOfIso g j hK (e ≪≫ s)).hom.app M =
      (upperShriekStdIsoFNewShriekOfIso g j hK e).hom.app M ≫
        (dualIntoMapIso s).hom.app ((pull g.left).op.obj ((dualInto K).rightOp.obj M.obj)) := by
  refine (upperShriekStdIsoFNewShriekOfIso_hom_app g j hK (e ≪≫ s) M).trans (Eq.trans ?_
    (congrArg (· ≫ _) (upperShriekStdIsoFNewShriekOfIso_hom_app g j hK e M)).symm)
  exact upperShriekStdIsoFNewShriekOfIso_trans_chase _ _ _ _ _ _ _ _ _
    ((dualIntoMapIso s).hom.app _) (Functor.map_comp _ _ _)
    ((Category.id_comp _).trans (Category.comp_id _).symm)
    ((dualIntoMapIso s).hom.naturality _)

/-- `upperShriekStdIsoFNewShriekOfIso_trans` for the inverses. -/
theorem upperShriekStdIsoFNewShriekOfIso_trans_inv {T : Scheme.{u}} [IsNoetherian T]
    {A B : FTS T} (g : A ⟶ B) (j : CompactificationOf (Over.mk g.left)) {K : Std B.left}
    (hK : IsDualizing K) {ω ω' : Std A.left} (e : upperShriekDualizing g j hK ≅ ω) (s : ω ≅ ω')
    (M : (plusCoh B.left).FullSubcategory) :
    (upperShriekStdIsoFNewShriekOfIso g j hK (e ≪≫ s)).inv.app M =
      (dualIntoMapIso s).inv.app ((pull g.left).op.obj ((dualInto K).rightOp.obj M.obj)) ≫
        (upperShriekStdIsoFNewShriekOfIso g j hK e).inv.app M :=
  inv_eq_inv_comp_inv_of_hom_eq_comp ((upperShriekStdIsoFNewShriekOfIso g j hK (e ≪≫ s)).app M)
    ((upperShriekStdIsoFNewShriekOfIso g j hK e).app M) ((dualIntoMapIso s).app _)
    (upperShriekStdIsoFNewShriekOfIso_trans g j hK e s M)

/-- `f_new^!` restricted to an open along equal morphisms. -/
theorem fNewShriekRestrictIso_congr {V X Y : Scheme.{u}} (ι : V ⟶ X) [IsOpenImmersion ι]
    (f : X ⟶ Y) {k k' : V ⟶ Y} (e : ι ≫ f = k) (hk : k = k') (ωX : Std X) (ωY : Std Y)
    (M : Std Y) :
    (fNewShriekRestrictIso ι f k e ωX ωY).hom.app M ≫ eqToHom (by subst hk; rfl) =
      (fNewShriekRestrictIso ι f k' (e.trans hk) ωX ωY).hom.app M := by
  subst hk
  rw [eqToHom_refl, Category.comp_id]

end Aux

/-! ### Changing the morphism of `FTS` along an equality -/

section Congr

variable {T : Scheme.{u}} [IsNoetherian T] {A B : FTS T}

/-- **The duality formula along equal morphisms**: for `g = g'`, compactifications `j` of `g` and
`j'` of `g'`, the isomorphism `g'^! ≅ g'_new^!` at `j'` and `e` is the one at `j` and the
identification of `g^!K` with `g'^!K`. -/
theorem upperShriekStdIsoFNewShriekOfIso_congr {g g' : A ⟶ B} (H : g = g')
    (j : CompactificationOf (Over.mk g.left)) (j' : CompactificationOf (Over.mk g'.left))
    {K : Std B.left} (hK : IsDualizing K) {ω : Std A.left}
    (e : upperShriekDualizing g' j' hK ≅ ω) (M : (plusCoh B.left).FullSubcategory) :
    (toStd A.left).map ((upperShriekPlusCongr H j j').hom.app (plusOfStd M)) ≫
        (upperShriekStdIsoFNewShriekOfIso g' j' hK e).hom.app M =
      (upperShriekStdIsoFNewShriekOfIso g j hK
          ((toStd A.left).mapIso ((upperShriekPlusCongr H j j').app
            (plusOfStd ⟨K, plusCoh_of_isDualizing hK⟩)) ≪≫ e)).hom.app M ≫
        eqToHom (by subst H; rfl) := by
  subst H
  rw [eqToHom_refl, Category.comp_id]
  exact upperShriekStdIsoFNewShriekOfIso_upperShriekPlusIso g j j' hK
    (plusOfStd ⟨K, plusCoh_of_isDualizing hK⟩).property M (plusOfStd M).property e

/-- `upperShriekStdIsoFNewShriekOfIso_congr` for the inverses. -/
theorem upperShriekStdIsoFNewShriekOfIso_congr_inv {g g' : A ⟶ B} (H : g = g')
    (j : CompactificationOf (Over.mk g.left)) (j' : CompactificationOf (Over.mk g'.left))
    {K : Std B.left} (hK : IsDualizing K) {ω : Std A.left}
    (e : upperShriekDualizing g' j' hK ≅ ω) (M : (plusCoh B.left).FullSubcategory) :
    (upperShriekStdIsoFNewShriekOfIso g' j' hK e).inv.app M ≫
        (toStd A.left).map ((upperShriekPlusCongr H j j').inv.app (plusOfStd M)) =
      eqToHom (by subst H; rfl) ≫
        (upperShriekStdIsoFNewShriekOfIso g j hK
          ((toStd A.left).mapIso ((upperShriekPlusCongr H j j').app
            (plusOfStd ⟨K, plusCoh_of_isDualizing hK⟩)) ≪≫ e)).inv.app M := by
  subst H
  rw [eqToHom_refl, Category.id_comp]
  exact inv_comp_inv_eq_inv_of_hom_comp_eq ((toStd A.left).mapIso
    ((upperShriekPlusCongr rfl j j').app (plusOfStd M)))
    ((upperShriekStdIsoFNewShriekOfIso g j' hK e).app M)
    ((upperShriekStdIsoFNewShriekOfIso g j hK ((toStd A.left).mapIso ((upperShriekPlusCongr rfl j
      j').app (plusOfStd ⟨K, plusCoh_of_isDualizing hK⟩)) ≪≫ e)).app M)
    ((upperShriekStdIsoFNewShriekOfIso_congr rfl j j' hK e M).trans
      (by rw [eqToHom_refl, Category.comp_id]; rfl))

end Congr

/-! ### The restriction of a compactification at the standard model -/

section PrecompOpen

variable {S : Scheme.{u}} [IsNoetherian S] {X' X Y : FTS S} (h : X' ⟶ X) [IsOpenImmersion h.left]
  (g : X ⟶ Y) (j : CompactificationOf (Over.mk g.left))

/-- **`(h ≫ g)^! ≅ Lh^* ∘ g^!` at the restricted compactification, read at the standard model**,
is the inverse of `Stacks.Duality.UpperShriekDuality.upperShriekStdRestrictIso`. -/
theorem upperShriekPrecompOpenIso_std (M : (plusCoh Y.left).FullSubcategory) :
    (comparison X'.left).inverse.map ((upperShriekPrecompOpenIso h g j).hom.app
        (toQCoh ⟨M.obj, plusCoh_le_qcoh _ M.property⟩)).hom ≫
      (pullModelConj h.left).hom.app
        ((upperShriek g j).obj (toQCoh ⟨M.obj, plusCoh_le_qcoh _ M.property⟩)).obj =
    (upperShriekStdRestrictIso h g j).inv.app M := by
  have P := pullModelConj_hom_app_comp_pullCompIso h.left j.immersion (h.left ≫ j.immersion) rfl
    ((twistedInverseImage j.toBase
        (isQuasicoherent_homology_derivedPushforward_of_qcqs j.toBase)).obj
      (toQCoh ⟨M.obj, plusCoh_le_qcoh _ M.property⟩)).obj
  rw [eqToHom_refl, Category.comp_id] at P
  have hpre : (comparison X'.left).inverse.map ((upperShriekPrecompOpenIso h g j).hom.app
        (toQCoh ⟨M.obj, plusCoh_le_qcoh _ M.property⟩)).hom =
      ((comparison X'.left).inverse.mapIso ((Stacks.Duality.derivedPullbackCompIso h.left
        j.immersion).app ((twistedInverseImage j.toBase
          (isQuasicoherent_homology_derivedPushforward_of_qcqs j.toBase)).obj
            (toQCoh ⟨M.obj, plusCoh_le_qcoh _ M.property⟩)).obj)).inv :=
    Eq.trans (by rfl) (congrArg (comparison X'.left).inverse.map (Category.comp_id _))
  exact (congrArg (· ≫ _) hpre).trans (upperShriekPrecompOpenIso_std_chase (pull h.left) _ _
    ((upperShriekStdIso g j).app M)
    ((pullCompIso h.left j.immersion (h.left ≫ j.immersion) rfl).app _)
    ((upperShriekStdIso (h ≫ g) (j.precompOpen h.left)).app M)
    ((upperShriekStdRestrictIso h g j).app M)
    (upperShriekStdRestrictIso_hom_app h g j M) P)

/-- `Lh^* g^!K ≅ (h ≫ g)^!K` for a dualizing `K` is the component of
`Lh^* ∘ g^! ≅ (h ≫ g)^!` at `K`. -/
theorem upperShriekDualizingRestrictIso_eq_app {K : Std Y.left} (hK : IsDualizing K) :
    upperShriekDualizingRestrictIso h g j hK =
      (upperShriekStdRestrictIso h g j).app ⟨K, plusCoh_of_isDualizing hK⟩ := by
  ext
  rw [Iso.app_hom, upperShriekStdRestrictIso_hom_app]
  rfl

end PrecompOpen

/-- `j^! ≅ j^!` at one compactification is the identity, for a morphism of `FTS` of the form
`ftsHomOf k`. -/
theorem upperShriekPlusIso_ftsHomOf_refl {Y V : Scheme.{u}} [IsNoetherian Y] {k : V ⟶ Y}
    (hk : IsShriekable k) (j : CompactificationOf (Over.mk k))
    (K : quasiCoherentDerivedCategoryPlusOfModel Y) :
    ((DominatingCompactification.upperShriekPlusIso
      (ftsHomOf k hk.separatedFiniteType (isSeparatedFiniteType_id Y) (Category.comp_id k))
        j j).hom.app K).hom = 𝟙 _ :=
  congrArg (fun i => (i.hom.app K).hom)
    (upperShriekPlusIso_refl
      (ftsHomOf k hk.separatedFiniteType (isSeparatedFiniteType_id Y) (Category.comp_id k)) j)

/-! ### Restricting to a smaller open -/

section Restrict

variable {X S : Scheme.{u}} {p : X ⟶ S} {W' W : X.Opens} (hle : W' ≤ W)
  (hW : IsShriekable (W.ι ≫ p)) (hW' : IsShriekable (W'.ι ≫ p))

/-- `W' ⊆ W` as a morphism of `FTS_S`. -/
abbrev restrictHom :
    ftsOf (W'.ι ≫ p) hW'.separatedFiniteType ⟶ ftsOf (W.ι ≫ p) hW.separatedFiniteType :=
  ftsHomOf (X.homOfLE hle) hW'.separatedFiniteType hW.separatedFiniteType
    (by rw [← Category.assoc, Scheme.homOfLE_ι])

/-- The underlying morphism of `restrictHom` is an open immersion. -/
instance isOpenImmersion_restrictHom_left : IsOpenImmersion (restrictHom hle hW hW').left :=
  inferInstanceAs (IsOpenImmersion (X.homOfLE hle))

/-- The compactification `c (W → S)` restricted to `W' ⊆ W`. -/
abbrev restrictCompactification :
    CompactificationOf (Over.mk (restrictHom hle hW hW' ≫ ftsHomSelf hW).left) :=
  @CompactificationOf.precompOpen _ (Over.mk (ftsHomSelf hW).left) (c (ftsHomSelf hW).left hW) _
    (restrictHom hle hW hW').left (isOpenImmersion_restrictHom_left hle hW hW')

/-- The composite of `W' ⊆ W` with `W → S` is `W' → S`. -/
theorem restrictHom_comp : restrictHom hle hW hW' ≫ ftsHomSelf hW = ftsHomSelf hW' := by
  ext
  exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ p) (Scheme.homOfLE_ι X hle))

/-- The underlying morphism of `restrictHom` is the inclusion `X.homOfLE hle`. -/
@[simp]
theorem restrictHom_left : (restrictHom hle hW hW').left = X.homOfLE hle := rfl

/-- The underlying scheme of `ftsOf q hq` is the source of `q`. -/
@[simp]
theorem ftsOf_left_eq {T Z : Scheme.{u}} (q : Z ⟶ T) (hq : isSeparatedFiniteType q) :
    (ftsOf q hq).left = Z := rfl

/-- The underlying morphism of `ftsHomSelf hq` is `q`. -/
@[simp]
theorem ftsHomSelf_left_eq {Z T : Scheme.{u}} {q : Z ⟶ T} (hq : IsShriekable q) :
    (ftsHomSelf hq).left = q := rfl

/-- The inclusion `W' ⊆ W` followed by `W → S` is the structure morphism `W' → S`. -/
theorem homOfLE_comp_structure : X.homOfLE hle ≫ W.ι ≫ p = W'.ι ≫ p := by
  rw [← Category.assoc, Scheme.homOfLE_ι]

variable [IsNoetherian S] (hh : IsShriekable (X.homOfLE hle))

/-- **`k^! ≅ h^! ∘ g^!` for `h : W' ⊆ W` at the standard model**: the comparison of the formalism
of compactifications, followed by `h^! = Lh^*`, is the change of compactification of `W' → S`
to the one of `W → S` restricted to `W'`, followed by `Lh^* ∘ g^! ≅ (h ≫ g)^!` there. -/
theorem factorIsoOf_shriekStdIso (M : (plusCoh S).FullSubcategory) :
    (toStd W'.toScheme).map ((UpperShriek.factorIsoOf c (homOfLE_comp_structure hle) hh hW
        hW').hom.app (plusOfStd M)) ≫
      (shriekStdIso c (X.homOfLE hle) hh).hom.app
        ((UpperShriek.shriekOf c (W.ι ≫ p) hW).obj (plusOfStd M)) =
    (toStd W'.toScheme).map ((upperShriekPlusCongr (restrictHom_comp hle hW hW').symm
        (c _ hW') (restrictCompactification c hle hW hW')).hom.app (plusOfStd M)) ≫
      (upperShriekStdRestrictIso (restrictHom hle hW hW') (ftsHomSelf hW) (c _ hW)).inv.app M := by
  have F := UpperShriek.factorIsoOf_hom_app_comp_shriekOfIsoPullbackOfIsOpenImmersion c
    (homOfLE_comp_structure hle) hh hW hW' (c _ hW) (c _ hW') (plusOfStd M)
  have F2 := comp_eq_comp_of_id_chase (quasiCoherentDerivedPullback' (X.homOfLE hle)) _ _ _ _ _ _ F
    (upperShriekPlusIso_ftsHomOf_refl hW' (c _ hW') (plusOfStd M))
    (upperShriekPlusIso_ftsHomOf_refl hW (c _ hW) (plusOfStd M))
  exact (congrArg _ (shriekStdIso_hom_app c (X.homOfLE hle) hh _)).trans
    (map_comp_paste_chase (ObjectProperty.ι _ ⋙ (comparison W'.toScheme).inverse) _ _ _ _ _ _ F2
      (upperShriekPrecompOpenIso_std (restrictHom hle hW hW') (ftsHomSelf hW) (c _ hW) M))

end Restrict

/-- The inverse of the restriction of a normalization, for the formalism of compactifications. -/
theorem restrictLocalIso_inv_ofCompactifications {X S : Scheme.{u}} {p : X ⟶ S}
    (hp : IsFiniteTypeOverNoetherian p) (ωS : quasiCoherentDerivedCategoryPlusOfModel S)
    (K : quasiCoherentDerivedCategoryPlusOfModel X) {W' W : X.Opens} (hle : W' ≤ W)
    (hW : IsShriekable (W.ι ≫ p))
    (α : (UpperShriek.ofCompactifications c).restrictTo hp W K ≅
      (UpperShriek.ofCompactifications c).localModel hW ωS) :
    ((UpperShriek.ofCompactifications c).restrictLocalIso hp ωS K hle hW α).inv =
      ((UpperShriek.factorIsoOf c (homOfLE_comp_structure hle) (hp.isShriekable_homOfLE hle) hW
          (hp.isShriekable_le hle hW)).hom.app ωS ≫
        (UpperShriek.shriekOf c (X.homOfLE hle) (hp.isShriekable_homOfLE hle)).map α.inv) ≫
        (UpperShriek.factorIsoOf c (X.homOfLE_ι hle) (hp.isShriekable_homOfLE hle)
          (hp.isShriekable_ι W) (hp.isShriekable_ι W')).inv.app K :=
  rfl

/-! ### The normalizations restrict -/

section Compat

variable {X S : Scheme.{u}} [IsNoetherian S] {p : X ⟶ S} {hp : IsFiniteTypeOverNoetherian p}
  {ωS : quasiCoherentDerivedCategoryPlusOfModel S}
  (𝒦X : NormalizedOnOpens (UpperShriek.ofCompactifications c) hp ωS)
  (hK : IsDualizing ((toStd S).obj ωS))
  {W' W : X.Opens} (hle : W' ≤ W) (hW : IsShriekable (W.ι ≫ p))
  (hW' : IsShriekable (W'.ι ≫ p))

/-- **The normalizations at the standard model restrict**: the one on `W'` is the restriction of
the one on `W`, through the change of compactification of `W' → S` and `Lh^* ∘ (W → S)^! ≅
(W' → S)^!`. -/
theorem normalizationPullIso_restrict :
    (toStd W'.toScheme).mapIso ((upperShriekPlusCongr (restrictHom_comp hle hW hW').symm
        (c _ hW') (restrictCompactification c hle hW hW')).app
          (plusOfStd ⟨(toStd S).obj ωS, plusCoh_of_isDualizing hK⟩)) ≪≫
      (upperShriekDualizingRestrictIso (restrictHom hle hW hW') (ftsHomSelf hW) (c _ hW)
        hK).symm ≪≫
      (pull (restrictHom hle hW hW').left).mapIso (normalizationPullIso c 𝒦X hK W hW) =
    normalizationPullIso c 𝒦X hK W' hW' ≪≫
      ((pullCompIso (restrictHom hle hW hW').left W.ι W'.ι (X.homOfLE_ι hle)).app
        (stdComplex c 𝒦X)).symm := by
  have hh := hp.isShriekable_homOfLE hle
  have hι := hp.isShriekable_ι W
  have hι' := hp.isShriekable_ι W'
  have hc := congrArg (fun i => (toStd W'.toScheme).map i.inv) (𝒦X.compat hle hW hW')
  have Hα : (toStd W'.toScheme).map (𝒦X.localIso W' hW').inv =
      (toStd W'.toScheme).map ((UpperShriek.factorIsoOf c (homOfLE_comp_structure hle) hh hW
        hW').hom.app ωS) ≫
      (toStd W'.toScheme).map ((UpperShriek.shriekOf c (X.homOfLE hle) hh).map
        (𝒦X.localIso W hW).inv) ≫
      (toStd W'.toScheme).map ((UpperShriek.factorIsoOf c (X.homOfLE_ι hle) hh hι hι').inv.app
        𝒦X.complex) :=
    hc.symm.trans ((congrArg (toStd W'.toScheme).map
      (restrictLocalIso_inv_ofCompactifications c hp ωS 𝒦X.complex hle hW _)).trans
      (((toStd W'.toScheme).map_comp _ _).trans
        ((congrArg (· ≫ _) ((toStd W'.toScheme).map_comp _ _)).trans (Category.assoc _ _ _))))
  have P1 := shriekStdIso_factorIso c (X.homOfLE_ι hle) hh hι hι' 𝒦X.complex
  have hfx := ((toStd W'.toScheme).map_comp _ _).symm.trans ((congrArg (toStd W'.toScheme).map
    ((UpperShriek.factorIsoOf c (X.homOfLE_ι hle) hh hι hι').inv_hom_id_app 𝒦X.complex)).trans
      ((toStd W'.toScheme).map_id _))
  have natfS := ((toStd W'.toScheme).map_comp _ _).symm.trans ((congrArg (toStd W'.toScheme).map
    ((UpperShriek.factorIsoOf c (homOfLE_comp_structure hle) hh hW hW').hom.naturality
      (plusOfStdIso ωS (plusCoh_of_isDualizing hK)).hom)).trans ((toStd W'.toScheme).map_comp _ _))
  have hsh := (congrArg (toStd W'.toScheme).map
    ((UpperShriek.shriekOf c (X.homOfLE hle) hh).map_comp
      ((UpperShriek.shriekOf c (W.ι ≫ p) hW).map (plusOfStdIso ωS (plusCoh_of_isDualizing hK)).hom)
      (𝒦X.localIso W hW).inv)).trans ((toStd W'.toScheme).map_comp _ _)
  have natSh := (shriekStdIso c (X.homOfLE hle) hh).hom.naturality
    ((UpperShriek.shriekOf c (W.ι ≫ p) hW).map (plusOfStdIso ωS (plusCoh_of_isDualizing hK)).hom ≫
      (𝒦X.localIso W hW).inv)
  have P3 := factorIsoOf_shriekStdIso c hle hW hW' hh ⟨(toStd S).obj ωS, plusCoh_of_isDualizing hK⟩
  have hDR := congrArg Iso.inv (upperShriekDualizingRestrictIso_eq_app (restrictHom hle hW hW')
    (ftsHomSelf hW) (c _ hW) hK)
  exact Iso.ext (normalizationPullIso_restrict_chase (pull (restrictHom hle hW hW').left)
    (hca' := (toStd W'.toScheme).map_comp _ _) (Hα := Hα) (P1 := P1) (hfx := hfx)
    (natfS := natfS) (hsh := hsh) (natSh := natSh) (P3 := P3) (hDR := hDR))

/-- **The comparisons on separated opens restrict**: for `W' ⊆ W` and `M ∈ D^+_Coh(𝒪_S)`, the
comparison `(p_new^! M)|_{W'} ≅ (W' → S)^! M` is the restriction of the one on `W`, through
`Lh^* Lι_W^* ≅ Lι_{W'}^*`, `h^! = Lh^*` and `(W' → S)^! ≅ h^! (W → S)^!`. -/
theorem restrictNewShriekIso_restrict (M : (plusCoh S).FullSubcategory) :
    (pullCompIso (restrictHom hle hW hW').left W.ι W'.ι (X.homOfLE_ι hle)).inv.app
        ((fNewShriekStd p (stdComplex c 𝒦X) ((toStd S).obj ωS)).obj
          ((plusCoh (ftsOf (𝟙 S) (isSeparatedFiniteType_id S)).left).ι.obj M)) ≫
      (pull (restrictHom hle hW hW').left).map
        ((@fNewShriekRestrictIso (ftsOf (W.ι ≫ p) hW.separatedFiniteType).left X
          (ftsOf (𝟙 S) (isSeparatedFiniteType_id S)).left W.ι
          (inferInstanceAs (IsOpenImmersion W.ι))
          p (ftsHomSelf hW).left rfl (stdComplex c 𝒦X) ((toStd S).obj ωS)).hom.app
            ((plusCoh (ftsOf (𝟙 S) (isSeparatedFiniteType_id S)).left).ι.obj M) ≫
          (upperShriekStdIsoFNewShriekOfIso (ftsHomSelf hW) (c _ hW) hK
            (normalizationPullIso c 𝒦X hK W hW)).inv.app M) ≫
      ((shriekStdIso c (X.homOfLE hle) (hp.isShriekable_homOfLE hle)).app
        ((UpperShriek.shriekOf c (W.ι ≫ p) hW).obj (plusOfStd M))).inv ≫
      (toStd W'.toScheme).map ((UpperShriek.factorIsoOf c (homOfLE_comp_structure hle)
        (hp.isShriekable_homOfLE hle) hW hW').inv.app (plusOfStd M)) =
    (@fNewShriekRestrictIso (ftsOf (W'.ι ≫ p) hW'.separatedFiniteType).left X
        (ftsOf (𝟙 S) (isSeparatedFiniteType_id S)).left W'.ι
        (inferInstanceAs (IsOpenImmersion W'.ι))
        p (ftsHomSelf hW').left rfl (stdComplex c 𝒦X) ((toStd S).obj ωS)).hom.app
          ((plusCoh (ftsOf (𝟙 S) (isSeparatedFiniteType_id S)).left).ι.obj M) ≫
      (upperShriekStdIsoFNewShriekOfIso (ftsHomSelf hW') (c _ hW') hK
        (normalizationPullIso c 𝒦X hK W' hW')).inv.app M := by
  have hh := hp.isShriekable_homOfLE hle
  have A := factorIsoOf_shriekStdIso c hle hW hW' hh M
  have A' := inv_comp_inv_eq_of_hom_comp_eq ((toStd W'.toScheme).mapIso
    ((UpperShriek.factorIsoOf c (homOfLE_comp_structure hle) hh hW hW').app (plusOfStd M)))
    ((shriekStdIso c (X.homOfLE hle) hh).app _)
    ((toStd W'.toScheme).mapIso ((upperShriekPlusCongr (restrictHom_comp hle hW hW').symm
      (c _ hW') (restrictCompactification c hle hW hW')).app (plusOfStd M)))
    ((upperShriekStdRestrictIso (restrictHom hle hW hW') (ftsHomSelf hW) (c _ hW)).app M).symm A
  have B := upperShriekStdIsoFNewShriekOfIso_restrict (restrictHom hle hW hW') (ftsHomSelf hW)
    (c _ hW) hK (normalizationPullIso c 𝒦X hK W hW) M
  have B0 := map_inv_app_comp_eq_comp_inv_app (M := M) (G' := (plusCoh S).ι ⋙
    fNewShriekStd (restrictHom hle hW hW' ≫ ftsHomSelf hW).left
      ((pull (restrictHom hle hW hW').left).obj ((pull W.ι).obj (stdComplex c 𝒦X)))
      ((toStd S).obj ωS)) _ _ _ B
  have C' := upperShriekStdIsoFNewShriekOfIso_congr_inv (restrictHom_comp hle hW hW').symm
    (c _ hW') (restrictCompactification c hle hW hW') hK
    ((upperShriekDualizingRestrictIso (restrictHom hle hW hW') (ftsHomSelf hW) (c _ hW)
      hK).symm ≪≫ (pull (restrictHom hle hW hW').left).mapIso
        (normalizationPullIso c 𝒦X hK W hW)) M
  have Dd := congrArg (fun e => (upperShriekStdIsoFNewShriekOfIso (ftsHomSelf hW') (c _ hW') hK
    e).inv.app M) (normalizationPullIso_restrict c 𝒦X hK hle hW hW')
  have Tr := upperShriekStdIsoFNewShriekOfIso_trans_inv (ftsHomSelf hW') (c _ hW') hK
    (normalizationPullIso c 𝒦X hK W' hW') (@id ((pull W'.ι).obj (stdComplex c 𝒦X) ≅
      (pull (restrictHom hle hW hW').left).obj ((pull W.ι).obj (stdComplex c 𝒦X)))
        ((pullCompIso (restrictHom hle hW hW').left W.ι W'.ι
          (X.homOfLE_ι hle)).app (stdComplex c 𝒦X)).symm) M
  have Fc := fNewShriekRestrictIso_congr (restrictHom hle hW hW').left (ftsHomSelf hW).left
    (rfl : (restrictHom hle hW hW').left ≫ (ftsHomSelf hW).left =
      (restrictHom hle hW hW' ≫ ftsHomSelf hW).left)
    (congrArg (fun φ => φ.left) (restrictHom_comp hle hW hW'))
    ((pull W.ι).obj (stdComplex c 𝒦X)) ((toStd S).obj ωS)
    ((plusCoh (ftsOf (𝟙 S) (isSeparatedFiniteType_id S)).left).ι.obj M)
  have G := @fNewShriekRestrictIso_comp _ _ (ftsOf (𝟙 S) (isSeparatedFiniteType_id S)).left _
    (restrictHom hle hW hW').left W.ι W'.ι (isOpenImmersion_restrictHom_left hle hW hW')
    (inferInstanceAs (IsOpenImmersion W.ι)) (inferInstanceAs (IsOpenImmersion W'.ι))
    (X.homOfLE_ι hle) p (ftsHomSelf hW).left (ftsHomSelf hW').left rfl rfl
    (congrArg (fun φ => φ.left) (restrictHom_comp hle hW hW'))
    (stdComplex c 𝒦X) ((toStd S).obj ωS)
    ((plusCoh (ftsOf (𝟙 S) (isSeparatedFiniteType_id S)).left).ι.obj M)
  have A'' : (((shriekStdIso c (X.homOfLE hle) hh).app
        ((UpperShriek.shriekOf c (W.ι ≫ p) hW).obj (plusOfStd M))).inv :
        (pull (restrictHom hle hW hW').left).obj
          ((upperShriekStd (ftsHomSelf hW) (c _ hW)).obj M) ⟶ _) ≫
      (toStd W'.toScheme).map ((UpperShriek.factorIsoOf c (homOfLE_comp_structure hle) hh hW
        hW').inv.app (plusOfStd M)) =
      (upperShriekStdRestrictIso (restrictHom hle hW hW') (ftsHomSelf hW) (c _ hW)).hom.app M ≫
        (toStd W'.toScheme).map ((upperShriekPlusCongr (restrictHom_comp hle hW hW').symm (c _ hW')
          (restrictCompactification c hle hW hW')).inv.app (plusOfStd M)) := A'
  have key := restrictNewShriekIso_restrict_chase (pull (restrictHom hle hW hW').left)
    (ow' := (upperShriekStdIsoFNewShriekOfIso (ftsHomSelf hW') (c _ hW') hK
      (normalizationPullIso c 𝒦X hK W' hW')).inv.app M)
    (A := A'') (B := B0) (C := C') (G := G)
    (hdi := Iso.inv_hom_id_app (dualIntoMapIso ((pullCompIso (restrictHom hle hW hW').left W.ι
      W'.ι (X.homOfLE_ι hle)).app (stdComplex c 𝒦X))) _)
    (F := eq_of_heq (HEq.trans (by heq_congr) (HEq.trans (heq_of_eq Fc) (by heq_congr))))
    (D := eq_of_heq (HEq.trans (by heq_congr) (HEq.trans (heq_of_eq (Dd.trans Tr))
      (by heq_congr))))
  exact key

/-- `restrictNewShriekIso_restrict` with the restriction along `W' ⊆ W` written as the morphism of
schemes `X.homOfLE`. -/
theorem restrictNewShriekIso_restrict' (M : (plusCoh S).FullSubcategory) :
    (pullCompIso (X.homOfLE hle) W.ι W'.ι (X.homOfLE_ι hle)).inv.app
        ((fNewShriekStd p (stdComplex c 𝒦X) ((toStd S).obj ωS)).obj
          ((plusCoh (ftsOf (𝟙 S) (isSeparatedFiniteType_id S)).left).ι.obj M)) ≫
      (pull (X.homOfLE hle)).map
        ((@fNewShriekRestrictIso (ftsOf (W.ι ≫ p) hW.separatedFiniteType).left X
          (ftsOf (𝟙 S) (isSeparatedFiniteType_id S)).left W.ι
          (inferInstanceAs (IsOpenImmersion W.ι))
          p (ftsHomSelf hW).left rfl (stdComplex c 𝒦X) ((toStd S).obj ωS)).hom.app
            ((plusCoh (ftsOf (𝟙 S) (isSeparatedFiniteType_id S)).left).ι.obj M) ≫
          (upperShriekStdIsoFNewShriekOfIso (ftsHomSelf hW) (c _ hW) hK
            (normalizationPullIso c 𝒦X hK W hW)).inv.app M) ≫
      (shriekStdIso c (X.homOfLE hle) (hp.isShriekable_homOfLE hle)).inv.app
        ((UpperShriek.shriekOf c (W.ι ≫ p) hW).obj (plusOfStd M)) ≫
      (toStd W'.toScheme).map ((UpperShriek.factorIsoOf c (homOfLE_comp_structure hle)
        (hp.isShriekable_homOfLE hle) hW hW').inv.app (plusOfStd M)) =
    (@fNewShriekRestrictIso (ftsOf (W'.ι ≫ p) hW'.separatedFiniteType).left X
        (ftsOf (𝟙 S) (isSeparatedFiniteType_id S)).left W'.ι
        (inferInstanceAs (IsOpenImmersion W'.ι))
        p (ftsHomSelf hW').left rfl (stdComplex c 𝒦X) ((toStd S).obj ωS)).hom.app
          ((plusCoh (ftsOf (𝟙 S) (isSeparatedFiniteType_id S)).left).ι.obj M) ≫
      (upperShriekStdIsoFNewShriekOfIso (ftsHomSelf hW') (c _ hW') hK
        (normalizationPullIso c 𝒦X hK W' hW')).inv.app M :=
  eq_of_heq (HEq.trans (by heq_congr) (HEq.trans
    (heq_of_eq (restrictNewShriekIso_restrict c 𝒦X hK hle hW hW' M)) (by heq_congr)))

end Compat

/-! ### `p_new^! ω_S'^•` is normalized relative to `ω_S'^•` -/

section Twist

variable {X S : Scheme.{u}} [IsNoetherian S] {p : X ⟶ S} {hp : IsFiniteTypeOverNoetherian p}
  {ωS ωS' : quasiCoherentDerivedCategoryPlusOfModel S}
  (𝒦X : NormalizedOnOpens (UpperShriek.ofCompactifications c) hp ωS)
  (hωS : IsDualizingComplex ωS.obj.obj) (hωS' : IsDualizingComplex ωS'.obj.obj)

/-- `p_new^! ω_S'^• = R𝓗om(Lp^* R𝓗om(ω_S'^•, ω_S^•), ω_X^•)` at the standard model. -/
abbrev twistStd : Std X :=
  (fNewShriekStd p (stdComplex c 𝒦X) ((toStd S).obj ωS)).obj ((toStd S).obj ωS')

include hωS hωS' in
/-- `p_new^! ω_S'^•` at the standard model lies in `D^+_Coh(𝒪_X)`. -/
theorem plusCoh_twistStd :
    haveI := hp.source_noetherian; plusCoh X (twistStd c (ωS' := ωS') 𝒦X) :=
  have := hp.source_noetherian
  plusCoh_fNewShriek p (isDualizing_stdComplex c hωS 𝒦X)
    (isDualizing_toStd hωS) _ (plusCoh_of_isDualizing (isDualizing_toStd hωS'))

/-- `p_new^! ω_S'^•` as an object of `D^+_QCoh(𝒪_X)` at the locally small model. -/
abbrev twist : quasiCoherentDerivedCategoryPlusOfModel X :=
  have := hp.source_noetherian
  plusOfStd ⟨twistStd c (ωS' := ωS') 𝒦X, plusCoh_twistStd c 𝒦X hωS hωS'⟩

/-- The normalization of `p_new^! ω_S'^•` on an open `W` separated over `S`. -/
def twistLocalIso (W : X.Opens) (hW : IsShriekable (W.ι ≫ p)) :
    (UpperShriek.ofCompactifications c).restrictTo hp W (twist c 𝒦X hωS hωS') ≅
      (UpperShriek.ofCompactifications c).localModel hW ωS' :=
  (toStd W.toScheme).preimageIso
    ((shriekStdIso c W.ι (hp.isShriekable_ι W)).app (twist c 𝒦X hωS hωS') ≪≫
      (pull W.ι).mapIso (have := hp.source_noetherian;
        ((comparison X).unitIso.app (twistStd c (ωS' := ωS') 𝒦X)).symm) ≪≫
      ((@fNewShriekRestrictIso (ftsOf (W.ι ≫ p) hW.separatedFiniteType).left X
        (ftsOf (𝟙 S) (isSeparatedFiniteType_id S)).left W.ι (inferInstanceAs (IsOpenImmersion W.ι))
        p (ftsHomSelf hW).left rfl (stdComplex c 𝒦X) ((toStd S).obj ωS)).app
          ((plusCoh (ftsOf (𝟙 S) (isSeparatedFiniteType_id S)).left).ι.obj
            ⟨(toStd S).obj ωS', plusCoh_of_isDualizing (isDualizing_toStd hωS')⟩) ≪≫
      ((upperShriekStdIsoFNewShriekOfIso (ftsHomSelf hW) (c _ hW) (isDualizing_toStd hωS)
        (normalizationPullIso c 𝒦X (isDualizing_toStd hωS) W hW)).app
          ⟨(toStd S).obj ωS', plusCoh_of_isDualizing (isDualizing_toStd hωS')⟩).symm) ≪≫
      (toStd W.toScheme).mapIso ((UpperShriek.shriekOf c (W.ι ≫ p) hW).mapIso
        (plusOfStdIso ωS' (plusCoh_of_isDualizing (isDualizing_toStd hωS')))))

/-- **`p_new^! ω_S'^•` is normalized relative to `ω_S'^•`.** -/
def twistNormalized : NormalizedOnOpens (UpperShriek.ofCompactifications c) hp ωS' where
  complex := twist c 𝒦X hωS hωS'
  localIso W hW := twistLocalIso c 𝒦X hωS hωS' W hW
  compat {W' W} h hW hW' := by
    have hh := hp.isShriekable_homOfLE h
    have hK := isDualizing_toStd hωS
    have hK' := plusCoh_of_isDualizing (isDualizing_toStd hωS')
    let T := twist c 𝒦X hωS hωS'
    have N1 := (shriekStdIso c (X.homOfLE h) hh).hom.naturality
      (twistLocalIso c 𝒦X hωS hωS' W hW).hom
    have hφ := Functor.map_preimage (toStd W.toScheme)
      ((shriekStdIso c W.ι (hp.isShriekable_ι W)).app T ≪≫
        (pull W.ι).mapIso (have := hp.source_noetherian;
          ((comparison X).unitIso.app (twistStd c (ωS' := ωS') 𝒦X)).symm) ≪≫
        ((@fNewShriekRestrictIso (ftsOf (W.ι ≫ p) hW.separatedFiniteType).left X
          (ftsOf (𝟙 S) (isSeparatedFiniteType_id S)).left W.ι
          (inferInstanceAs (IsOpenImmersion W.ι)) p (ftsHomSelf hW).left rfl (stdComplex c 𝒦X)
          ((toStd S).obj ωS)).app
            ((plusCoh (ftsOf (𝟙 S) (isSeparatedFiniteType_id S)).left).ι.obj
              ⟨(toStd S).obj ωS', hK'⟩) ≪≫
        ((upperShriekStdIsoFNewShriekOfIso (ftsHomSelf hW) (c _ hW) hK
          (normalizationPullIso c 𝒦X hK W hW)).app ⟨(toStd S).obj ωS', hK'⟩).symm) ≪≫
        (toStd W.toScheme).mapIso ((UpperShriek.shriekOf c (W.ι ≫ p) hW).mapIso
          (plusOfStdIso ωS' hK'))).hom
    have P1 := shriekStdIso_factorIso c (X.homOfLE_ι h) hh (hp.isShriekable_ι W)
      (hp.isShriekable_ι W') T
    have Nu := ((pullCompIso (X.homOfLE h) W.ι W'.ι (X.homOfLE_ι h)).inv.naturality
      (X := (toStd X).obj T) (Y := twistStd c (ωS' := ωS') 𝒦X)
      (have := hp.source_noetherian;
        ((comparison X).unitIso.app (twistStd c (ωS' := ωS') 𝒦X)).symm).hom).symm
    have C := restrictNewShriekIso_restrict' c 𝒦X hK h hW hW' ⟨(toStd S).obj ωS', hK'⟩
    have Nc1 := (shriekStdIso c (X.homOfLE h) hh).inv.naturality
      ((UpperShriek.shriekOf c (W.ι ≫ p) hW).map (plusOfStdIso ωS' hK').hom)
    have Nc2 := ((toStd W'.toScheme).map_comp _ _).symm.trans ((congrArg (toStd W'.toScheme).map
      ((UpperShriek.factorIsoOf c (homOfLE_comp_structure h) hh hW hW').inv.naturality
        (plusOfStdIso ωS' hK').hom)).trans ((toStd W'.toScheme).map_comp _ _))
    have hsh := Iso.hom_inv_id_app (shriekStdIso c (X.homOfLE h) hh)
      ((UpperShriek.shriekOf c (W.ι ≫ p) hW).obj ωS')
    apply Iso.ext
    apply (toStd W'.toScheme).map_injective
    refine (((toStd W'.toScheme).map_comp _ _).trans
      (congrArg (_ ≫ ·) ((toStd W'.toScheme).map_comp _ _))).trans ?_
    refine Eq.trans ?_ (Functor.map_preimage _ _).symm
    exact twistLocalIso_compat_chase (pull (X.homOfLE h)) (N1 := N1) (hφ := hφ) (P1 := P1)
      (Nu := Nu) (Nc1 := Nc1) (Nc2 := Nc2) (hsh := hsh)
      (C := eq_of_heq (HEq.trans (by heq_congr) (HEq.trans (heq_of_eq C) (by heq_congr))))

end Twist

/-! ### The normalized complex for the second dualizing complex -/

section Independence

variable {X S : Scheme.{u}} {p : X ⟶ S} {hp : IsFiniteTypeOverNoetherian p}
  {ωS ωS' : quasiCoherentDerivedCategoryPlusOfModel S}

/-- **The complex normalized relative to `ω_S'^•` is `p_new^! ω_S'^•`**, formed with the complex
`ω_X^•` normalized relative to `ω_S^•`:
`ω_X'^• ≅ R𝓗om(Lp^* R𝓗om(ω_S'^•, ω_S^•), ω_X^•)`. -/
def stdComplexIsoTwist (hωS : haveI := hp.base_noetherian; IsDualizingComplex ωS.obj.obj)
    (hωS' : haveI := hp.base_noetherian; IsDualizingComplex ωS'.obj.obj)
    (𝒦X : NormalizedOnOpens (UpperShriek.ofCompactifications c) hp ωS)
    (𝒦X' : NormalizedOnOpens (UpperShriek.ofCompactifications c) hp ωS') :
    stdComplex c 𝒦X' ≅
      (fNewShriekStd p (stdComplex c 𝒦X) ((toStd S).obj ωS)).obj ((toStd S).obj ωS') :=
  have := hp.base_noetherian
  (toStd X).mapIso (existsUnique_iso_ofCompactifications c hωS' 𝒦X'
      (twistNormalized c 𝒦X hωS hωS')).exists.choose ≪≫
    ((comparison X).unitIso.app _).symm

variable {Y : Scheme.{u}} {f : X ⟶ Y} {q : Y ⟶ S} {hq : IsFiniteTypeOverNoetherian q}

/-- **`ω_X'^• ≅ f_new^! ω_Y'^•`**: for `f : X ⟶ Y` over `S`, the complex normalized relative to
`ω_S'^•` upstairs is `f_new^!` of the one downstairs, `f_new^!` being formed with the complexes
normalized relative to `ω_S^•`. -/
def stdComplexIsoFNewShriek (hpe : f ≫ q = p)
    (hωS : haveI := hp.base_noetherian; IsDualizingComplex ωS.obj.obj)
    (hωS' : haveI := hp.base_noetherian; IsDualizingComplex ωS'.obj.obj)
    (𝒦X : NormalizedOnOpens (UpperShriek.ofCompactifications c) hp ωS)
    (𝒦Y : NormalizedOnOpens (UpperShriek.ofCompactifications c) hq ωS)
    (𝒦X' : NormalizedOnOpens (UpperShriek.ofCompactifications c) hp ωS')
    (𝒦Y' : NormalizedOnOpens (UpperShriek.ofCompactifications c) hq ωS') :
    stdComplex c 𝒦X' ≅
      (fNewShriekStd f (stdComplex c 𝒦X) (stdComplex c 𝒦Y)).obj (stdComplex c 𝒦Y') :=
  have := hp.base_noetherian
  have := hq.source_noetherian
  have := isIso_fNewShriekCompHom_app hpe (stdComplex c 𝒦X)
    (isDualizing_stdComplex c hωS 𝒦Y) (isDualizing_toStd hωS)
    ((toStd S).obj ωS') (plusCoh_of_isDualizing (isDualizing_toStd hωS'))
  stdComplexIsoTwist c hωS hωS' 𝒦X 𝒦X' ≪≫
    (asIso ((fNewShriekCompHom hpe (stdComplex c 𝒦X) (stdComplex c 𝒦Y)
      ((toStd S).obj ωS)).app ((toStd S).obj ωS'))).symm ≪≫
    (fNewShriekStd f (stdComplex c 𝒦X) (stdComplex c 𝒦Y)).mapIso
      (stdComplexIsoTwist c hωS hωS' 𝒦Y 𝒦Y').symm

/-- **Stacks Project, Tag 0BV3.** Let `S` be a Noetherian scheme with a dualizing complex `ω_S^•`
and let `f : X ⟶ Y` be a morphism of schemes of finite type over `S`. Then the functor

`f_new^! = D_X ∘ Lf^* ∘ D_Y : D^+_Coh(𝒪_Y) ⥤ D(𝒪_X)`

of [Stacks, Tag 0AUE], formed with the dualizing complexes `ω_X^•`, `ω_Y^•` normalized relative to
`ω_S^•`, does not depend on `ω_S^•` up to canonical isomorphism: for a second dualizing complex
`ω_S'^•` on `S`, with `ω_X'^•`, `ω_Y'^•` normalized relative to it, the two functors are
isomorphic. (It takes values in `D^+_Coh(𝒪_X)`, `Stacks.Duality.plusCoh_fNewShriek`.)

The proof: `ω_X'^• ≅ f_new^! ω_Y'^•` (`stdComplexIsoFNewShriek`), and then
`Stacks.Duality.fNewShriekStdIsoOfIso`, which uses that `R𝓗om(ω_Y'^•, ω_Y^•)` is invertible
([Stacks, Tag 0ATP]). -/
@[stacks 0BV3]
def fNewShriekIndependenceIso (hpe : f ≫ q = p)
    (hωS : haveI := hp.base_noetherian; IsDualizingComplex ωS.obj.obj)
    (hωS' : haveI := hp.base_noetherian; IsDualizingComplex ωS'.obj.obj)
    (𝒦X : NormalizedOnOpens (UpperShriek.ofCompactifications c) hp ωS)
    (𝒦Y : NormalizedOnOpens (UpperShriek.ofCompactifications c) hq ωS)
    (𝒦X' : NormalizedOnOpens (UpperShriek.ofCompactifications c) hp ωS')
    (𝒦Y' : NormalizedOnOpens (UpperShriek.ofCompactifications c) hq ωS') :
    (plusCoh Y).ι ⋙ fNewShriekStd f (stdComplex c 𝒦X') (stdComplex c 𝒦Y') ≅
      (plusCoh Y).ι ⋙ fNewShriekStd f (stdComplex c 𝒦X) (stdComplex c 𝒦Y) :=
  have := hq.source_noetherian
  Functor.isoWhiskerLeft _ (fNewShriekStdIsoOfIso f
    (isDualizing_stdComplex c hωS 𝒦Y)
    (isDualizing_stdComplex c hωS' 𝒦Y')
    (stdComplexIsoFNewShriek c hpe hωS hωS' 𝒦X 𝒦Y 𝒦X' 𝒦Y'))

end Independence

end Stacks.Duality.NormalizedOnOpens

end
