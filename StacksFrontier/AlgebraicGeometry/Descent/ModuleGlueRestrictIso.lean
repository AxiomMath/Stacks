module

public import StacksFrontier.AlgebraicGeometry.Descent.ZariskiModuleGlueDescent

/-!
# Glueing data of modules from isomorphisms of restrictions

`Stacks.SheafOfModules.ModulesGlueData`, the shape in which Stacks 00AM is consumed in algebraic
geometry, gives its transitions as linear equivalences of sections over the opens contained in
two charts. This file constructs such glueing data from isomorphisms of sheaves of modules.

The input is a family of isomorphisms
`iso i j : (f i)_* (mod i)|_V ≅ (f j)_* (mod j)|_V`
of the restrictions to an open `V` of `S` contained in the ranges of the `i`-th and the `j`-th
chart, compatible with shrinking `V` and satisfying the cocycle condition on triple overlaps.
`AlgebraicGeometry.RestrictIsoGlueData.toModulesGlueData` turns such a family into glueing data,
whence a module on `S` restricting to `mod i` along each chart. This is the route
`AlgebraicGeometry.modulesGlueDataOfDescentData` takes for a descent datum along a covering by
open subschemes; here the charts are arbitrary open immersions `f i : Z i ⟶ S`, so the
construction applies to modules on schemes that are merely isomorphic to opens of `S`.

## Main definitions

* `AlgebraicGeometry.RestrictIsoGlueData`: the comparison data of a family of modules on charts,
  phrased by isomorphisms of restrictions rather than by equivalences of sections.
* `AlgebraicGeometry.RestrictIsoGlueData.toModulesGlueData`: **the glueing datum it determines.**
* `AlgebraicGeometry.RestrictIsoGlueData.glued` and
  `AlgebraicGeometry.RestrictIsoGlueData.chartIso`: the glued module and its identification with
  the module on each chart.

## Main results

* `AlgebraicGeometry.restrictLocal_comp` and `AlgebraicGeometry.restrictLocal_id`: restriction of
  a morphism of restrictions to a smaller open is functorial.
* `AlgebraicGeometry.RestrictIsoGlueData.trans_map` and
  `AlgebraicGeometry.RestrictIsoGlueData.trans_trans`: the two compatibilities of the resulting
  equivalences of sections.
* `AlgebraicGeometry.RestrictIsoGlueData.isQuasicoherent_glued`: **the glued module is
  quasi-coherent** when the charts cover `S` and the modules on the charts are quasi-coherent.

## References

* [Stacks Project, Tag 00AM](https://stacks.math.columbia.edu/tag/00AM)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace Limits
open Stacks.SheafOfModules
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-! ### Functoriality of the restriction of a morphism of restrictions -/

section RestrictLocal

variable {X : Scheme.{u}} {A B C : X.Modules} {V W : X.Opens}

/-- **Restriction to a smaller open is functorial.** -/
theorem restrictLocal_comp (φ : Scheme.Modules.restrict A W.ι ⟶ Scheme.Modules.restrict B W.ι)
    (ψ : Scheme.Modules.restrict B W.ι ⟶ Scheme.Modules.restrict C W.ι) (hV : V ≤ W) :
    restrictLocal (φ ≫ ψ) hV = restrictLocal φ hV ≫ restrictLocal ψ hV := by
  simp only [restrictLocal, Functor.map_comp, Category.assoc]
  congr 1
  simp only [← Category.assoc]
  congr 1
  simp

/-- **Restriction to a smaller open is unital.** -/
theorem restrictLocal_id (hV : V ≤ W) :
    restrictLocal (𝟙 (Scheme.Modules.restrict A W.ι)) hV = 𝟙 _ := by
  simp [restrictLocal]

end RestrictLocal

/-! ### Comparison data phrased by isomorphisms of restrictions -/

/-- **Comparison data of a family of modules on charts, phrased categorically.**  The charts are
open immersions `f i : Z i ⟶ S` from arbitrary schemes; the `i`-th carries a sheaf of modules
`mod i`, and over every open `V` of `S` inside the ranges of the `i`-th and the `j`-th chart the
direct images of `mod i` and `mod j` are identified after restriction to `V`, compatibly with
shrinking `V` and satisfying the cocycle condition. -/
structure RestrictIsoGlueData (S : Scheme.{u}) {ι : Type u} {Z : ι → Scheme.{u}}
    (f : ∀ i, Z i ⟶ S) [∀ i, IsOpenImmersion (f i)] where
  /-- The sheaf of modules carried by the `i`-th chart. -/
  mod : ∀ i, (Z i).Modules
  /-- The comparison isomorphism over an open `V` of `S` inside two chart ranges, as an
  isomorphism of the restrictions to `V` of the two direct images. -/
  iso : ∀ (i j : ι) {V : S.Opens}, V ≤ (f i).opensRange → V ≤ (f j).opensRange →
    (Scheme.Modules.restrict ((Scheme.Modules.pushforward (f i)).obj (mod i)) V.ι ≅
      Scheme.Modules.restrict ((Scheme.Modules.pushforward (f j)).obj (mod j)) V.ι)
  /-- The comparison isomorphisms are compatible with shrinking the open. -/
  iso_restrict : ∀ (i j : ι) {V V' : S.Opens} (hi : V ≤ (f i).opensRange)
      (hj : V ≤ (f j).opensRange) (hV' : V' ≤ V),
    restrictLocal (iso i j hi hj).hom hV' = (iso i j (hV'.trans hi) (hV'.trans hj)).hom
  /-- The cocycle condition on the triple overlaps. -/
  iso_trans : ∀ (i j k : ι) {V : S.Opens} (hi : V ≤ (f i).opensRange)
      (hj : V ≤ (f j).opensRange) (hk : V ≤ (f k).opensRange),
    (iso i j hi hj).hom ≫ (iso j k hj hk).hom = (iso i k hi hk).hom

namespace RestrictIsoGlueData

variable {S : Scheme.{u}} {ι : Type u} {Z : ι → Scheme.{u}} {f : ∀ i, Z i ⟶ S}
  [∀ i, IsOpenImmersion (f i)] (D : RestrictIsoGlueData S f)

/-- The transition of the comparison data, read on sections over `V` as a linear equivalence. -/
noncomputable def trans (i j : ι) {V : S.Opens} (hi : V ≤ (f i).opensRange)
    (hj : V ≤ (f j).opensRange) :
    openSections (f i) (D.mod i) V ≃ₗ[ToType (S.ringCatSheaf.obj.obj (op V))]
      openSections (f j) (D.mod j) V :=
  localAppEquiv (D.iso i j hi hj) V le_rfl

/-- The transition applied to a section `s` over `V` is the component over `V` of the comparison
isomorphism applied to `s`. -/
theorem trans_apply (i j : ι) {V : S.Opens} (hi : V ≤ (f i).opensRange)
    (hj : V ≤ (f j).opensRange) (s : ToType (openSections (f i) (D.mod i) V)) :
    D.trans i j hi hj s = localAppFun (D.iso i j hi hj).hom V le_rfl s := rfl

/-- The transition over a smaller open is the transition over the larger one, read there. -/
theorem trans_eq_localAppFun_le (i j : ι) {V V' : S.Opens} (hi : V ≤ (f i).opensRange)
    (hj : V ≤ (f j).opensRange) (hV' : V' ≤ V)
    (s : ToType (openSections (f i) (D.mod i) V')) :
    D.trans i j (hV'.trans hi) (hV'.trans hj) s =
      localAppFun (D.iso i j hi hj).hom V' hV' s := by
  rw [trans_apply, ← D.iso_restrict i j hi hj hV']
  exact congrFun (congrArg (fun g ↦ (ConcreteCategory.hom g : _ → _))
    (localApp_restrictLocal (D.iso i j hi hj).hom hV').symm) s

/-- **The transitions commute with restriction of sections.** -/
theorem trans_map (i j : ι) {V W : S.Opens} (hi : V ≤ (f i).opensRange)
    (hj : V ≤ (f j).opensRange) (hWV : W ≤ V)
    (s : ToType (openSections (f i) (D.mod i) V)) :
    D.trans i j (hWV.trans hi) (hWV.trans hj)
        (((Scheme.Modules.pushforward (f i)).obj (D.mod i)).val.map (homOfLE hWV).op s)
      = ((Scheme.Modules.pushforward (f j)).obj (D.mod j)).val.map (homOfLE hWV).op
          (D.trans i j hi hj s) :=
  (D.trans_eq_localAppFun_le i j hi hj hWV _).trans
    (localAppFun_naturality (D.iso i j hi hj).hom le_rfl hWV (homOfLE hWV) s).symm

/-- **The cocycle condition for the transitions.** -/
theorem trans_trans (i j k : ι) {V : S.Opens} (hi : V ≤ (f i).opensRange)
    (hj : V ≤ (f j).opensRange) (hk : V ≤ (f k).opensRange)
    (s : ToType (openSections (f i) (D.mod i) V)) :
    D.trans j k hj hk (D.trans i j hi hj s) = D.trans i k hi hk s := by
  rw [trans_apply, trans_apply, trans_apply,
    ← localAppFun_comp (D.iso i j hi hj).hom (D.iso j k hj hk).hom V le_rfl s,
    D.iso_trans i j k hi hj hk]

/-- **The glueing datum determined by comparison data phrased categorically.** -/
noncomputable def toModulesGlueData : ModulesGlueData S f where
  mod := D.mod
  trans i j {_V} hi hj := D.trans i j hi hj
  trans_map i j {_V _W} hi hj hWV s := D.trans_map i j hi hj hWV s
  trans_trans i j k {_V} hi hj hk s := D.trans_trans i j k hi hj hk s

/-- The module on each chart of the glueing datum is the module of the comparison data. -/
@[simp] theorem toModulesGlueData_mod : D.toModulesGlueData.mod = D.mod := rfl

/-- **The module on `S` glued from comparison data phrased categorically.** -/
noncomputable abbrev glued : S.Modules := D.toModulesGlueData.glued

/-- **The glued module restricts along each chart to the module that chart carried.** -/
noncomputable def chartIso (i : ι) : Scheme.Modules.restrict D.glued (f i) ≅ D.mod i :=
  D.toModulesGlueData.chartIso i

/-- **The glued module is quasi-coherent** as soon as the chart ranges cover `S` and each module
on a chart is quasi-coherent. -/
theorem isQuasicoherent_glued (hf : ⨆ i, (f i).opensRange = ⊤)
    (hmod : ∀ i, (D.mod i).IsQuasicoherent) : D.glued.IsQuasicoherent := by
  refine isQuasicoherent_of_restrict_openCover D.glued (fun i ↦ (f i).opensRange) hf fun i ↦ ?_
  have h1 : ((Scheme.Modules.pullback (f i)).obj D.glued).IsQuasicoherent :=
    Stacks.Descent.isQuasicoherent_of_iso
      ((D.chartIso i).symm ≪≫
        (Scheme.Modules.restrictFunctorIsoPullback (f i)).app D.glued) (hmod i)
  refine Stacks.Descent.isQuasicoherent_of_iso
    ((Scheme.Modules.restrictFunctorIsoPullback ((f i).opensRange).ι).app D.glued).symm ?_
  refine Stacks.Descent.isQuasicoherent_of_iso
    ((Scheme.Modules.pullbackComp (f i).isoOpensRange.inv (f i)).app D.glued ≪≫
      (Scheme.Modules.pullbackCongr (Scheme.Hom.isoOpensRange_inv_comp (f i))).app D.glued) ?_
  exact Stacks.Modules.isQuasicoherent_pullback (f i).isoOpensRange.inv _ h1

end RestrictIsoGlueData

end AlgebraicGeometry

end
