module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.Coverings
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparisonTopologies
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleOpenOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.EtaleCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.KernelPairRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactTopology
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.Zariski
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCoverAffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCoveringPoints
public import StacksFrontier.RingTheory.BeauvilleLaszlo.GlueableModule
public import StacksFrontier.RingTheory.BeauvilleLaszlo.Surjectivity

/-!
# Glueability of an algebraic space is étale local

Fix a Beauville--Laszlo glueing pair `(g : R → R', f)`. A module over `R` is *glueable* when it
is recovered from its two base changes; this module transfers that notion to an algebraic space
`Y` over `Spec R` by asking it of the global sections of the affine schemes étale over `Y`, and
shows that the condition may equivalently be tested on a single étale covering of `Y` by affine
schemes.

## Main definitions

* `AlgebraicGeometry.Space.IsGlueableGlobalSections`: glueability of the global sections of an
  object of the big fppf site over `Spec R`, with their canonical `R`-module structure.
* `AlgebraicGeometry.Space.IsGlueableAlgebraicSpace`: glueability of every affine scheme étale
  over an algebraic space.

## Main results

* `AlgebraicGeometry.Space.exists_etaleCovering_iff_isGlueable`: **Stacks 0F9P**, the
  étale-local characterization of glueability.

## Implementation notes

The `R`-algebra structure on the global sections of an object of the site comes from its
structure morphism to `Spec R` together with the canonical isomorphism `R ≅ Γ(Spec R, 𝒪)`. An
étale covering is `AlgebraicGeometry.Space.IsEtaleCovering`, a family of morphisms from
algebraic spaces which is jointly surjective on points and étale in each member.

The hard direction refines a given covering by affine charts: quasi-compactness of each affine
chart of `Y` makes finitely many members of the covering suffice over it, the resulting
finite family of charts is a Zariski covering of the chart, and glueability of a module is
local for a finite Zariski covering, which is what the exact sequence of the glueing pair
provides.

## References

* [Stacks Project, Tag 0F9P](https://stacks.math.columbia.edu/tag/0F9P)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry.Space

/-- The global sections of a scheme over `Spec R`, with the module structure
induced by its structure map, are glueable for `(R → R', f)`. -/
abbrev IsGlueableGlobalSections
    {R : Type u} {R' : Type v} [CommRing R] [CommRing R']
    (g : R →+* R') (f : R)
    (B : BigFppfSite.{u})
    (hX : B.Contains (Spec (.of R)))
    (W : BigFppfOver B (Spec (.of R)) hX) : Prop :=
  let T := (BigFppfOver.toScheme B (Spec (.of R)) hX).obj W
  letI : Algebra R R' := g.toAlgebra
  letI : Algebra R Γ(T, ⊤) :=
    (((Scheme.ΓSpecIso (.of R)).inv ≫
      (B.inclusion.map W.hom).appTop).hom).toAlgebra
  BeauvilleLaszlo.IsGlueableFor (S := R') Γ(T, ⊤) f

/-- An algebraic space is glueable for `(R → R', f)` if every affine scheme
étale over it has glueable global sections. -/
abbrev IsGlueableAlgebraicSpace
    {R : Type u} {R' : Type v} [CommRing R] [CommRing R']
    (g : R →+* R') (f : R)
    (B : BigFppfSite.{u})
    (hX : B.Contains (Spec (.of R)))
    (Y : _root_.AlgebraicGeometry.AlgebraicSpaces B (Spec (.of R)) hX) : Prop :=
  ∀ (W : BigFppfOver B (Spec (.of R)) hX)
      (p : yoneda.obj W ⟶ Y.1),
      IsAffine ((BigFppfOver.toScheme B (Spec (.of R)) hX).obj W) →
      IsEtale B (Spec (.of R)) hX p →
      IsGlueableGlobalSections g f B hX W

/-- The structure map of an object of the site over `Spec R` induces on global sections the
algebra map of the canonical `R`-algebra structure. -/
private theorem globalSections_algebraMap_comp
    {R : Type u} [CommRing R] (B : BigFppfSite.{u})
    (hX : B.Contains (Spec (.of R)))
    {V W : BigFppfOver B (Spec (.of R)) hX} (q : V ⟶ W) :
    (((Scheme.ΓSpecIso (.of R)).inv ≫ (B.inclusion.map V.hom).appTop).hom) =
    ((B.inclusion.map q.left).appTop.hom).comp
      (((Scheme.ΓSpecIso (.of R)).inv ≫ (B.inclusion.map W.hom).appTop).hom) := by
  show ((B.inclusion.map V.hom).appTop.hom).comp
      (Scheme.ΓSpecIso (.of R)).inv.hom =
    ((B.inclusion.map q.left).appTop.hom).comp
      (((B.inclusion.map W.hom).appTop.hom).comp
        (Scheme.ΓSpecIso (.of R)).inv.hom)
  have hq : (B.inclusion.map q.left).appTop.hom.comp
      (B.inclusion.map W.hom).appTop.hom =
      (B.inclusion.map V.hom).appTop.hom := by
    have h := congrArg (fun k => k.appTop.hom) (congrArg B.inclusion.map q.w)
    simpa only [Functor.map_comp, Scheme.Hom.comp_appTop, CommRingCat.hom_comp] using h
  exact (congrArg (fun z => z.comp (Scheme.ΓSpecIso (.of R)).inv.hom) hq).symm

/-- Glueability for a glueing pair is inherited by the base change of a module along a flat
algebra map: the two base-change tensor products and the comparison sequence are carried along
by the canonical identifications. -/
private theorem isGlueableFor_baseChange_of_flat_algebra
    {R : Type u} {S : Type v} {A : Type w} {A' : Type u}
    [CommRing R] [CommRing S] [CommRing A] [CommRing A'] [Algebra R S]
    [Algebra R A] [Algebra R A'] [Algebra A A'] [IsScalarTower R A A']
    (f : R) (hflat : Module.Flat A A') :
    (BeauvilleLaszlo.IsGlueableFor (S := S) A f →
      BeauvilleLaszlo.IsGlueableFor (S := S) A' f) ∧
    (Module.FaithfullyFlat A A' →
      BeauvilleLaszlo.IsGlueableFor (S := S) A' f →
      BeauvilleLaszlo.IsGlueableFor (S := S) A f) := by
  classical
  let : Module.Flat A A' := hflat
  let X := TensorProduct R A S
  let Y := TensorProduct R A (Localization.Away f)
  let Z := TensorProduct R A (Localization.Away (algebraMap R S f))
  let X' := TensorProduct R A' S
  let Y' := TensorProduct R A' (Localization.Away f)
  let Z' := TensorProduct R A' (Localization.Away (algebraMap R S f))
  let : Algebra A X := Algebra.TensorProduct.leftAlgebra
  let : Algebra A Y := Algebra.TensorProduct.leftAlgebra
  let : Algebra A Z := Algebra.TensorProduct.leftAlgebra
  let : Algebra A' X' := Algebra.TensorProduct.leftAlgebra
  let : Algebra A' Y' := Algebra.TensorProduct.leftAlgebra
  let : Algebra A' Z' := Algebra.TensorProduct.leftAlgebra
  let : Algebra A X' := Algebra.compHom X' (algebraMap A A')
  let : Algebra A Y' := Algebra.compHom Y' (algebraMap A A')
  let : Algebra A Z' := Algebra.compHom Z' (algebraMap A A')
  let d : A →ₗ[A] X × Y :=
    LinearMap.prod (Algebra.linearMap A X) (Algebra.linearMap A Y)
  let eS : S →ₗ[R] Localization.Away (algebraMap R S f) :=
    (IsScalarTower.toAlgHom R S (Localization.Away (algebraMap R S f))).toLinearMap
  let eR : Localization.Away f →ₗ[R] Localization.Away (algebraMap R S f) := {
    toFun := Localization.awayMap (algebraMap R S) f
    map_add' := map_add _
    map_smul' := by
      intro r x
      simp only [RingHom.id_apply, Algebra.smul_def]
      rw [map_mul]
      congr 1
      rw [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq]
      exact (IsScalarTower.algebraMap_apply R S
        (Localization.Away (algebraMap R S f)) r).symm
  }
  let b : X →ₗ[A] Z := TensorProduct.AlgebraTensorModule.map
    (LinearMap.id : A →ₗ[A] A) eS
  let c : Y →ₗ[A] Z := TensorProduct.AlgebraTensorModule.map
    (LinearMap.id : A →ₗ[A] A) eR
  let e : X × Y →ₗ[A] Z := LinearMap.coprod b (-c)
  let dR : A →ₗ[R] X × Y := d.restrictScalars R
  let eR' : X × Y →ₗ[R] Z := e.restrictScalars R
  let d' : A' →ₗ[A'] X' × Y' :=
    LinearMap.prod
      (Algebra.linearMap A' X')
      (Algebra.linearMap A' Y')
  let b' : X' →ₗ[A'] Z' := TensorProduct.AlgebraTensorModule.map
    (LinearMap.id : A' →ₗ[A'] A') eS
  let c' : Y' →ₗ[A'] Z' := TensorProduct.AlgebraTensorModule.map
    (LinearMap.id : A' →ₗ[A'] A') eR
  let e' : X' × Y' →ₗ[A'] Z' := LinearMap.coprod b' (-c')
  let d'' : A' →ₗ[R] X' × Y' := d'.restrictScalars R
  let e'' : X' × Y' →ₗ[R] Z' := e'.restrictScalars R
  have hd' : d'' = BeauvilleLaszlo.toTensorBaseChanges A' f := by
    ext a <;> rfl
  have he' : e'' = BeauvilleLaszlo.tensorAwayDifference A' f := by
    apply LinearMap.ext
    rintro ⟨x, y⟩
    show b' x - c' y =
      BeauvilleLaszlo.baseChangeToAway A' f x -
        BeauvilleLaszlo.localizedBaseChangeToAway A' f y
    rfl
  let e0 : TensorProduct A A' A ≃ₗ[A'] A' :=
    TensorProduct.AlgebraTensorModule.rid A A' A'
  let e1 : TensorProduct A A' (X × Y) ≃ₗ[A']
      TensorProduct A A' X × TensorProduct A A' Y :=
    TensorProduct.prodRight A A' A' X Y
  let eX : TensorProduct A A' X ≃ₗ[A'] X' :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange R A A' A' S
  let eY : TensorProduct A A' Y ≃ₗ[A'] Y' :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange R A A' A' (Localization.Away f)
  let e2 : TensorProduct A A' Z ≃ₗ[A'] Z' :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange R A A' A'
      (Localization.Away (algebraMap R S f))
  let E1 := e1.trans (eX.prodCongr eY)
  have hbase_d (x : TensorProduct A A' A) :
      E1 (d.baseChange A' x) = d' (e0 x) := by
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a a' =>
        simp [E1, d, d', e0, e1, eX, eY, LinearMap.baseChange,
          X, Y, X', Y',
          TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
          TensorProduct.prodRight_tmul,
          Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply]
  have hb (x : TensorProduct A A' X) :
      e2 (TensorProduct.AlgebraTensorModule.map
        (LinearMap.id : A' →ₗ[A'] A') b x) = b' (eX x) := by
    have h := TensorProduct.AlgebraTensorModule.lTensor_comp_cancelBaseChange
        (R := R) (A := A) (B := A') (M := A')
        (N := S) (Q := Localization.Away (algebraMap R S f)) eS
    have hmap : e2.toLinearMap.comp (TensorProduct.AlgebraTensorModule.map
        (LinearMap.id : A' →ₗ[A'] A') b) = b'.comp eX.toLinearMap := h.symm
    exact LinearMap.congr_fun hmap x
  have hc (x : TensorProduct A A' Y) :
      e2 (TensorProduct.AlgebraTensorModule.map
        (LinearMap.id : A' →ₗ[A'] A') c x) = c' (eY x) := by
    have h := TensorProduct.AlgebraTensorModule.lTensor_comp_cancelBaseChange
        (R := R) (A := A) (B := A') (M := A')
        (N := Localization.Away f) (Q := Localization.Away (algebraMap R S f)) eR
    have hmap : e2.toLinearMap.comp (TensorProduct.AlgebraTensorModule.map
        (LinearMap.id : A' →ₗ[A'] A') c) = c'.comp eY.toLinearMap := h.symm
    exact LinearMap.congr_fun hmap x
  have hbase_e (x : TensorProduct A A' (X × Y)) :
      e2 (e.baseChange A' x) = e' (E1 x) := by
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a xy =>
        rcases xy with ⟨x, y⟩
        show e2 (a ⊗ₜ[A] (b x - c y)) =
          b' (eX (a ⊗ₜ[A] x)) - c' (eY (a ⊗ₜ[A] y))
        rw [TensorProduct.tmul_sub, map_sub]
        have hb' := hb (a ⊗ₜ[A] x)
        have hc' := hc (a ⊗ₜ[A] y)
        simpa only [TensorProduct.AlgebraTensorModule.map_tmul, LinearMap.id_apply] using
          congrArg₂ (fun p q => p - q) hb' hc'
  have hbase_d' : d'.comp e0.toLinearMap = E1.toLinearMap.comp (d.baseChange A') :=
    LinearMap.ext (fun x => (hbase_d x).symm)
  have hbase_e' : e'.comp E1.toLinearMap = e2.toLinearMap.comp (e.baseChange A') :=
    LinearMap.ext (fun x => (hbase_e x).symm)
  constructor
  · intro hA
    rcases hA with ⟨hinj, hexact, hsurj⟩
    have hinjA : Function.Injective d := hinj
    have hexactA : Function.Exact d e := hexact
    have hsurjA : Function.Surjective e := hsurj
    refine ⟨?_, ?_, ?_⟩
    · intro x y hxy
      have hzero : Function.Exact (0 : Unit →ₗ[A] A) d :=
        (LinearMap.exact_zero_iff_injective Unit d).2 hinjA
      have hzero' : Function.Exact
          ((0 : Unit →ₗ[A] A).lTensor A') (d.lTensor A') :=
        Module.Flat.lTensor_exact A' hzero
      have hinj' : Function.Injective (d.lTensor A') :=
        (LinearMap.exact_zero_iff_injective (TensorProduct A A' Unit)
          (d.lTensor A')).1 (by simpa using hzero')
      have hinjBase : Function.Injective (d.baseChange A') := by
        simpa only [LinearMap.baseChange_eq_ltensor] using hinj'
      have hpre : e0.symm x = e0.symm y := by
        apply hinjBase
        apply E1.injective
        calc
          E1 (d.baseChange A' (e0.symm x)) = d' (e0 (e0.symm x)) := hbase_d _
          _ = d' x := congrArg d' (e0.apply_symm_apply x)
          _ = d' y := by
            simpa [d', X', Y', BeauvilleLaszlo.toTensorBaseChanges,
              Algebra.TensorProduct.algebraMap_apply] using hxy
          _ = E1 (d.baseChange A' (e0.symm y)) :=
            ((hbase_d (e0.symm y)).trans (congrArg d' (e0.apply_symm_apply y))).symm
      exact e0.symm.injective hpre
    · have hex' : Function.Exact (d.lTensor A') (e.lTensor A') :=
        Module.Flat.lTensor_exact A' hexactA
      have hexBase : Function.Exact (d.baseChange A') (e.baseChange A') := by
        simpa only [LinearMap.baseChange_eq_ltensor] using hex'
      exact (Function.Exact.iff_of_ladder_linearEquiv hbase_d' hbase_e').mpr hexBase
    · have hsurj' : Function.Surjective (e.lTensor A') := LinearMap.lTensor_surjective A' hsurjA
      have hsurjBase : Function.Surjective (e.baseChange A') := by
        simpa only [LinearMap.baseChange_eq_ltensor] using hsurj'
      intro z
      obtain ⟨x, hx⟩ := hsurjBase (e2.symm z)
      refine ⟨E1 x, ?_⟩
      show e' (E1 x) = z
      calc
        e' (E1 x) = e2 (e.baseChange A' x) := (hbase_e _).symm
        _ = e2 (e2.symm z) := by rw [hx]
        _ = z := e2.apply_symm_apply z
  · intro hFF
    let : Module.FaithfullyFlat A A' := hFF
    intro hA'
    rcases hA' with ⟨hinj', hexact', hsurj'⟩
    have hinjD' : Function.Injective d' := by
      show Function.Injective d''
      rw [hd']
      exact hinj'
    have hexactD' : Function.Exact d' e' := by
      show Function.Exact d'' e''
      rw [hd', he']
      exact hexact'
    have hsurjE' : Function.Surjective e' := by
      show Function.Surjective e''
      rw [he']
      exact hsurj'
    have hinjBase : Function.Injective (d.baseChange A') := by
      intro x y hxy
      apply e0.injective
      apply hinjD'
      calc
        d' (e0 x) = E1 (d.baseChange A' x) := (hbase_d x).symm
        _ = E1 (d.baseChange A' y) := congrArg E1 hxy
        _ = d' (e0 y) := hbase_d y
    have hinjTensor : Function.Injective (d.lTensor A') := by
      simpa only [LinearMap.baseChange_eq_ltensor] using hinjBase
    have hinjA : Function.Injective d :=
      (Module.FaithfullyFlat.lTensor_injective_iff_injective A A' d).1 hinjTensor
    have hexBase : Function.Exact (d.baseChange A') (e.baseChange A') :=
      (Function.Exact.iff_of_ladder_linearEquiv hbase_d' hbase_e').mp hexactD'
    have hexTensor : Function.Exact (d.lTensor A') (e.lTensor A') := by
      simpa only [LinearMap.baseChange_eq_ltensor] using hexBase
    have hexactA : Function.Exact d e :=
      (Module.FaithfullyFlat.lTensor_exact_iff_exact A A' d e).1 hexTensor
    have hsurjBase : Function.Surjective (e.baseChange A') := by
      intro z
      obtain ⟨w, hw⟩ := hsurjE' (e2 z)
      refine ⟨E1.symm w, ?_⟩
      apply e2.injective
      calc
        e2 (e.baseChange A' (E1.symm w)) = e' (E1 (E1.symm w)) := hbase_e _
        _ = e' w := congrArg e' (E1.apply_symm_apply w)
        _ = e2 z := hw
    have hsurjTensor : Function.Surjective (e.lTensor A') := by
      simpa only [LinearMap.baseChange_eq_ltensor] using hsurjBase
    have hsurjA : Function.Surjective e :=
      (Module.FaithfullyFlat.lTensor_surjective_iff_surjective A A' e).1 hsurjTensor
    exact ⟨hinjA, hexactA, hsurjA⟩

universe uA

/-- For a faithfully flat algebra map, glueability of a module and glueability of its base change
are equivalent. -/
private theorem isGlueableFor_iff_of_faithfullyFlat_algebra
    {R : Type u} {S : Type v} {A : Type uA} {A' : Type u}
    [CommRing R] [CommRing S] [CommRing A] [CommRing A'] [Algebra R S]
    [Algebra R A] [Algebra R A'] [Algebra A A'] [IsScalarTower R A A']
    (f : R) [Module.FaithfullyFlat A A'] :
    BeauvilleLaszlo.IsGlueableFor (S := S) A f ↔
      BeauvilleLaszlo.IsGlueableFor (S := S) A' f := by
  have h := isGlueableFor_baseChange_of_flat_algebra (R := R) (S := S)
    (A := A) (A' := A') f inferInstance
  exact ⟨h.1, fun hA' => h.2 inferInstance hA'⟩

/-- Glueability of global sections is inherited along a flat morphism of objects of the site, and
descends along a faithfully flat one. -/
private theorem isGlueableGlobalSections_of_flat_map
    {R : Type u} {R' : Type v} [CommRing R] [CommRing R']
    (g : R →+* R') (f : R)
    (B : BigFppfSite.{u})
    (hX : B.Contains (Spec (.of R)))
    (W V : BigFppfOver B (Spec (.of R)) hX)
    (q : V ⟶ W)
    (hWaff : IsAffine ((BigFppfOver.toScheme B (Spec (.of R)) hX).obj W))
    (hVaff : IsAffine ((BigFppfOver.toScheme B (Spec (.of R)) hX).obj V))
    (hflat : Flat ((BigFppfOver.toScheme B (Spec (.of R)) hX).map q)) :
    (IsGlueableGlobalSections g f B hX W → IsGlueableGlobalSections g f B hX V) ∧
      (((BigFppfOver.toScheme B (Spec (.of R)) hX).map q).appTop.hom.FaithfullyFlat →
        IsGlueableGlobalSections g f B hX V → IsGlueableGlobalSections g f B hX W) := by
  classical
  let G := BigFppfOver.toScheme B (Spec (.of R)) hX
  let T := G.obj W
  let T' := G.obj V
  let A := Γ(T, ⊤)
  let A' := Γ(T', ⊤)
  let : Algebra R R' := g.toAlgebra
  let : Algebra R A :=
    (((Scheme.ΓSpecIso (.of R)).inv ≫
      (B.inclusion.map W.hom).appTop).hom).toAlgebra
  let : Algebra R A' :=
    (((Scheme.ΓSpecIso (.of R)).inv ≫
      (B.inclusion.map V.hom).appTop).hom).toAlgebra
  let : Algebra A A' := (G.map q).appTop.hom.toAlgebra
  let : IsScalarTower R A A' :=
    IsScalarTower.of_algebraMap_eq' (globalSections_algebraMap_comp B hX q)
  have hflat' : Module.Flat A A' :=
    RingHom.flat_algebraMap_iff.mpr (G.map q).flat_appTop
  have h := isGlueableFor_baseChange_of_flat_algebra
    (R := R) (S := R') (A := A) (A' := A') f hflat'
  exact ⟨h.1, fun hff => h.2 hff⟩

universe uR uI uM uN uP

/-- A finite product of injective linear maps is injective. -/
private theorem injective_piLinearMap
    {R : Type uR} {I : Type uI} [Semiring R]
    {M : I → Type uM} {N : I → Type uN}
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]
    (f : ∀ i, M i →ₗ[R] N i) :
    Function.Injective (LinearMap.pi (fun i => (f i).comp (LinearMap.proj i))) ↔
      ∀ i, Function.Injective (f i) := by
  classical
  constructor
  · intro h i x y hxy
    let x' : ∀ j, M j := Pi.single i x
    let y' : ∀ j, M j := Pi.single i y
    have hmap :
        LinearMap.pi (fun j => (f j).comp (LinearMap.proj j)) x' =
          LinearMap.pi (fun j => (f j).comp (LinearMap.proj j)) y' := by
      ext j
      by_cases hj : j = i
      · subst j
        simpa [x', y'] using hxy
      · simp [x', y', hj]
    simpa [x', y'] using congrFun (h hmap) i
  · exact fun h x y hxy => funext fun i => h i (congrFun hxy i)

/-- A finite product of surjective linear maps is surjective. -/
private theorem surjective_piLinearMap
    {R : Type uR} {I : Type uI} [Semiring R]
    {M : I → Type uM} {N : I → Type uN}
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]
    (f : ∀ i, M i →ₗ[R] N i) :
    Function.Surjective (LinearMap.pi (fun i => (f i).comp (LinearMap.proj i))) ↔
      ∀ i, Function.Surjective (f i) := by
  classical
  constructor
  · intro h i z
    let z' : ∀ j, N j := Pi.single i z
    obtain ⟨x, hx⟩ := h z'
    exact ⟨x i, by simpa [z'] using congrFun hx i⟩
  · intro h z
    choose x hx using fun i => h i (z i)
    exact ⟨x, funext hx⟩

/-- A finite product of exact pairs of linear maps is exact. -/
private theorem exact_piLinearMap
    {R : Type uR} {I : Type uI} [Semiring R]
    {M : I → Type uM} {N : I → Type uN} {P : I → Type uP}
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]
    [∀ i, AddCommGroup (P i)] [∀ i, Module R (P i)]
    (f : ∀ i, M i →ₗ[R] N i) (g : ∀ i, N i →ₗ[R] P i) :
    Function.Exact (LinearMap.pi (fun i => (f i).comp (LinearMap.proj i)))
      (LinearMap.pi (fun i => (g i).comp (LinearMap.proj i))) ↔
      ∀ i, Function.Exact (f i) (g i) := by
  classical
  constructor
  · intro h i x
    constructor
    · intro hx
      let x' : ∀ j, N j := Pi.single i x
      have hx' : LinearMap.pi (fun j => (g j).comp (LinearMap.proj j)) x' = 0 := by
        ext j
        by_cases hj : j = i
        · subst j
          simpa [x'] using hx
        · simp [x', hj]
      obtain ⟨y, hy⟩ := (h x').mp hx'
      exact ⟨y i, by simpa [x'] using congrFun hy i⟩
    · rintro ⟨y, rfl⟩
      let y' : ∀ j, M j := Pi.single i y
      let x' : ∀ j, N j := Pi.single i (f i y)
      have hmap :
          LinearMap.pi (fun j => (f j).comp (LinearMap.proj j)) y' = x' := by
        ext j
        by_cases hj : j = i
        · subst j
          simp [y', x']
        · simp [y', x', hj]
      have hz := (h x').2 ⟨y', hmap⟩
      simpa [x'] using congrFun hz i
  · intro h x
    constructor
    · intro hx
      choose y hy using fun i => (h i (x i)).mp (by simpa using congrFun hx i)
      exact ⟨y, funext hy⟩
    · rintro ⟨y, rfl⟩
      ext i
      exact (h i (f i (y i))).2 ⟨y i, rfl⟩

/-- A finite product of modules is glueable exactly when each factor is: the defining sequence of
the product is the product of the defining sequences. -/
private theorem isGlueableFor_pi_iff
    {R : Type u} {S : Type v} {I : Type uI} {M : I → Type u}
    [CommRing R] [CommRing S] [Algebra R S]
    [Finite I]
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    (f : R) :
    BeauvilleLaszlo.IsGlueableFor (S := S) (∀ i, M i) f ↔
      ∀ i, BeauvilleLaszlo.IsGlueableFor (S := S) (M i) f := by
  classical
  let _ : Fintype I := Fintype.ofFinite I
  let eX : TensorProduct R (∀ i, M i) S ≃ₗ[R]
      ∀ i, TensorProduct R (M i) S := TensorProduct.piLeft R S M
  let eY : TensorProduct R (∀ i, M i) (Localization.Away f) ≃ₗ[R]
      ∀ i, TensorProduct R (M i) (Localization.Away f) :=
    TensorProduct.piLeft R (Localization.Away f) M
  let eZ : TensorProduct R (∀ i, M i)
      (Localization.Away (algebraMap R S f)) ≃ₗ[R]
      ∀ i, TensorProduct R (M i) (Localization.Away (algebraMap R S f)) :=
    TensorProduct.piLeft R (Localization.Away (algebraMap R S f)) M
  let eSwap : ((∀ i, TensorProduct R (M i) S) ×
      (∀ i, TensorProduct R (M i) (Localization.Away f))) ≃ₗ[R]
      ∀ i, (TensorProduct R (M i) S ×
        TensorProduct R (M i) (Localization.Away f)) := {
    toFun := fun x i => (x.1 i, x.2 i)
    invFun := fun x => (fun i => (x i).1, fun i => (x i).2)
    left_inv := by intro x; cases x; rfl
    right_inv := by intro x; funext i; exact Prod.ext rfl rfl
    map_add' := by intro x y; ext i <;> simp
    map_smul' := by intro r x; ext i <;> simp
  }
  let e1 := (eX.prodCongr eY).trans eSwap
  let d : (∀ i, M i) →ₗ[R]
      (TensorProduct R (∀ i, M i) S ×
        TensorProduct R (∀ i, M i) (Localization.Away f)) :=
    BeauvilleLaszlo.toTensorBaseChanges (∀ i, M i) f
  let e : (TensorProduct R (∀ i, M i) S ×
        TensorProduct R (∀ i, M i) (Localization.Away f)) →ₗ[R]
      TensorProduct R (∀ i, M i) (Localization.Away (algebraMap R S f)) :=
    BeauvilleLaszlo.tensorAwayDifference (∀ i, M i) f
  let eS (i : I) : (M i) →ₗ[R]
      (TensorProduct R (M i) S × TensorProduct R (M i) (Localization.Away f)) :=
    BeauvilleLaszlo.toTensorBaseChanges (M i) f
  let eT (i : I) : (TensorProduct R (M i) S ×
        TensorProduct R (M i) (Localization.Away f)) →ₗ[R]
      TensorProduct R (M i) (Localization.Away (algebraMap R S f)) :=
    BeauvilleLaszlo.tensorAwayDifference (M i) f
  let dπ : (∀ i, M i) →ₗ[R]
      ∀ i, (TensorProduct R (M i) S × TensorProduct R (M i) (Localization.Away f)) :=
    LinearMap.pi (fun i => (eS i).comp (LinearMap.proj i))
  let eπ : (∀ i, TensorProduct R (M i) S ×
        TensorProduct R (M i) (Localization.Away f)) →ₗ[R]
      ∀ i, TensorProduct R (M i) (Localization.Away (algebraMap R S f)) :=
    LinearMap.pi (fun i => (eT i).comp (LinearMap.proj i))
  have hd (x : ∀ i, M i) : e1 (d x) = dπ x := by
    ext i <;>
      simp [e1, eSwap, eX, eY, d, dπ, eS, TensorProduct.piLeft,
        TensorProduct.piRight, BeauvilleLaszlo.toTensorBaseChanges_apply]
  have hb (x : TensorProduct R (∀ i, M i) S) (i : I) :
      (eZ (BeauvilleLaszlo.baseChangeToAway (∀ i, M i) f x)) i =
        BeauvilleLaszlo.baseChangeToAway (M i) f (eX x i) := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp [hx, hy]
    | tmul m s =>
      simp [eZ, eX, TensorProduct.piLeft, TensorProduct.piRight,
        BeauvilleLaszlo.baseChangeToAway]
  have hc (x : TensorProduct R (∀ i, M i) (Localization.Away f)) (i : I) :
      (eZ (BeauvilleLaszlo.localizedBaseChangeToAway (∀ i, M i) f x)) i =
        BeauvilleLaszlo.localizedBaseChangeToAway (M i) f (eY x i) := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp [hx, hy]
    | tmul m s =>
      simp [eZ, eY, TensorProduct.piLeft, TensorProduct.piRight,
        BeauvilleLaszlo.localizedBaseChangeToAway]
  have he (x : TensorProduct R (∀ i, M i) S ×
      TensorProduct R (∀ i, M i) (Localization.Away f)) :
      eZ (e x) = eπ (e1 x) := by
    rcases x with ⟨x, y⟩
    ext i
    show eZ (BeauvilleLaszlo.baseChangeToAway (∀ i, M i) f x -
        BeauvilleLaszlo.localizedBaseChangeToAway (∀ i, M i) f y) i =
      BeauvilleLaszlo.tensorAwayDifference (M i) f (eX x i, eY y i)
    rw [map_sub, Pi.sub_apply, hb x i, hc y i]
    simp [BeauvilleLaszlo.tensorAwayDifference_apply]
  have hd' : dπ.comp (LinearEquiv.refl R (∀ i, M i)).toLinearMap =
      e1.toLinearMap.comp d := LinearMap.ext (fun x => (hd x).symm)
  have he' : eπ.comp e1.toLinearMap = eZ.toLinearMap.comp e := LinearMap.ext (fun x => (he x).symm)
  have hD_iff : Function.Injective d ↔ Function.Injective dπ := by
    constructor
    · intro h x y hxy
      apply h
      apply e1.injective
      calc
        e1 (d x) = dπ x := hd x
        _ = dπ y := hxy
        _ = e1 (d y) := (hd y).symm
    · intro h x y hxy
      apply h
      calc
        dπ x = e1 (d x) := (hd x).symm
        _ = e1 (d y) := congrArg e1 hxy
        _ = dπ y := hd y
  have hE_iff : Function.Exact d e ↔ Function.Exact dπ eπ :=
    (Function.Exact.iff_of_ladder_linearEquiv hd' he').symm
  show (Function.Injective d ∧ Function.Exact d e ∧ Function.Surjective e) ↔
      ∀ i, (Function.Injective (eS i) ∧ Function.Exact (eS i) (eT i) ∧
        Function.Surjective (eT i))
  constructor
  · rintro ⟨hD, hE, hS⟩
    have hDπ := hD_iff.mp hD
    have hEπ := hE_iff.mp hE
    have hSπ : Function.Surjective eπ := by
        intro z
        obtain ⟨x, hx⟩ := hS (eZ.symm z)
        refine ⟨e1 x, ?_⟩
        calc
          eπ (e1 x) = eZ (e x) := (he x).symm
          _ = z := by rw [hx]; exact eZ.apply_symm_apply z
    intro i
    exact ⟨(injective_piLinearMap (R := R) (I := I) (M := M)
          (N := fun i => TensorProduct R (M i) S ×
            TensorProduct R (M i) (Localization.Away f)) eS).mp hDπ i,
      (exact_piLinearMap (R := R) (I := I) (M := M)
          (N := fun i => TensorProduct R (M i) S ×
            TensorProduct R (M i) (Localization.Away f))
          (P := fun i => TensorProduct R (M i)
            (Localization.Away (algebraMap R S f))) eS eT).mp hEπ i,
      (surjective_piLinearMap (R := R) (I := I)
          (M := fun i => TensorProduct R (M i) S ×
            TensorProduct R (M i) (Localization.Away f))
          (N := fun i => TensorProduct R (M i)
            (Localization.Away (algebraMap R S f))) eT).mp hSπ i⟩
  · intro h
    have hDπ : Function.Injective dπ := by
      simpa [dπ, eS] using
        (injective_piLinearMap (R := R) (I := I) (M := M)
          (N := fun i => TensorProduct R (M i) S ×
            TensorProduct R (M i) (Localization.Away f)) eS).mpr
          (fun i => (h i).1)
    have hEπ : Function.Exact dπ eπ := by
      simpa [dπ, eπ, eS, eT] using
        (exact_piLinearMap (R := R) (I := I) (M := M)
          (N := fun i => TensorProduct R (M i) S ×
            TensorProduct R (M i) (Localization.Away f))
          (P := fun i => TensorProduct R (M i)
            (Localization.Away (algebraMap R S f))) eS eT).mpr
          (fun i => (h i).2.1)
    have hπ : Function.Surjective eπ := by
      simpa [eπ, eT] using
        (surjective_piLinearMap (R := R) (I := I)
          (M := fun i => TensorProduct R (M i) S ×
            TensorProduct R (M i) (Localization.Away f))
          (N := fun i => TensorProduct R (M i)
            (Localization.Away (algebraMap R S f))) eT).mpr
          (fun i => (h i).2.2)
    refine ⟨hD_iff.mpr hDπ, hE_iff.mpr hEπ, ?_⟩
    · intro z
      obtain ⟨x, hx⟩ := hπ (eZ z)
      refine ⟨e1.symm x, ?_⟩
      apply eZ.injective
      calc
        eZ (e (e1.symm x)) = eπ (e1 (e1.symm x)) := he _
        _ = eπ x := by rw [e1.apply_symm_apply]
        _ = eZ z := hx

/-- Restriction to the summands identifies the global sections of a coproduct of schemes with the
product of the global sections of the summands. -/
private lemma sigma_global_sections_bijective {ι : Type u} (Y : ι → Scheme.{u}) :
    Function.Bijective (fun (s : Γ(∐ Y, ⊤)) (i : ι) =>
      (Sigma.ι Y i).appTop.hom s) := by
  classical
  let T : Scheme.{u} := ∐ Y
  let O (i : ι) : T.Opens := Sigma.ι Y i ''ᵁ ⊤
  have hO : ⨆ i, O i = ⊤ := by
    simp only [O, Scheme.Hom.image_top_eq_opensRange]
    exact (sigmaOpenCover Y).iSup_opensRange
  let G : TopCat.Sheaf CommRingCat T.toTopCat := T.sheaf
  have hcompat (sf : ∀ i, Γ(T, O i)) :
      TopCat.Presheaf.IsCompatible G.1 O sf := by
    intro i j
    by_cases hij : i = j
    · subst j
      rfl
    · have hd : O i ⊓ O j = ⊥ := by
        simpa only [O, Scheme.Hom.image_top_eq_opensRange] using
          (disjoint_iff.mp (disjoint_opensRange_sigmaι Y i j hij))
      have : Subsingleton (G.obj.obj (Opposite.op (O i ⊓ O j))) := by
        rw [hd]
        exact CommRingCat.subsingleton_of_isTerminal T.sheaf.isTerminalOfEmpty
      exact Subsingleton.elim _ _
  have hres : Function.Bijective (fun (s : Γ(T, ⊤)) (i : ι) =>
      T.presheaf.map (homOfLE (le_top : O i ≤ ⊤)).op s) := by
    constructor
    · intro s t heq
      obtain ⟨gl, _, huniq⟩ := G.existsUnique_gluing' O ⊤
        (fun i => homOfLE le_top) (by rw [hO])
        (fun i => T.presheaf.map (homOfLE (le_top : O i ≤ ⊤)).op s) (hcompat _)
      exact (huniq s fun _ => rfl).trans (huniq t fun i => (congrFun heq i).symm).symm
    · intro sf
      obtain ⟨gl, hgl, _⟩ := G.existsUnique_gluing' O ⊤
        (fun i => homOfLE le_top) (by rw [hO]) sf (hcompat sf)
      exact ⟨gl, funext hgl⟩
  have hcomp (i : ι) (s : Γ(T, ⊤)) :
      (Sigma.ι Y i).appTop.hom s =
        ((Sigma.ι Y i).appIso ⊤).hom
          (T.presheaf.map (homOfLE (le_top : O i ≤ ⊤)).op s) := by
    let f : Y i ⟶ T := Sigma.ι Y i
    have hh : f.appTop ≫ (f.appIso ⊤).inv =
        T.presheaf.map (homOfLE (le_top : O i ≤ ⊤)).op := by
      convert f.app_appIso_inv ⊤ using 1 <;> rfl
    show f.appTop.hom s = (f.appIso ⊤).hom
      (T.presheaf.map (homOfLE (le_top : O i ≤ ⊤)).op s)
    rw [← hh]
    simp
  constructor
  · intro s t heq
    apply hres.1
    funext i
    have hi := congrArg (fun x => ((Sigma.ι Y i).appIso ⊤).inv x) (congrFun heq i)
    simpa only [hcomp, Iso.hom_inv_id_apply] using hi
  · intro sf
    obtain ⟨s, hs⟩ := hres.2 (fun i => ((Sigma.ι Y i).appIso ⊤).inv (sf i))
    refine ⟨s, funext (fun i => ?_)⟩
    simp only [hcomp, congrFun hs i]
    simp

/-- A Zariski covering of an algebraic space by open subspaces is an étale covering. -/
private theorem isEtaleCovering_of_isZariskiCover_subfunctor
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    {I : Type u} (X : I → Subfunctor F) (hX : IsZariskiCover B S hS I X) :
    IsEtaleCovering B S hS (fun i => (X i).toFunctor) (fun i => (X i).ι) :=
  isEtaleCovering_of_isZariskiCovering B S hS hF (fun i => (hX.1 i).1)
    ⟨fun i => (hX.1 i).2, by
      simpa only [Set.eq_univ_iff_forall, Set.mem_iUnion, Set.mem_range] using
        Set.eq_univ_iff_forall.mp ((isZariskiCover_iff_iUnion_points B S hS F hF I X hX.1).mp hX)⟩

/-- A surjective étale morphism from a representable presheaf into an algebraic space is an
étale covering by one member. -/
private theorem isEtaleCovering_punit_of_surjective_etale
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    {U : BigFppfOver B S hS} (q : yoneda.obj U ⟶ F)
    (hsurj : (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf q)
    (het : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf q) :
    IsEtaleCovering B S hS (fun _ : PUnit => yoneda.obj U) (fun _ => q) := by
  let : HasPullbacks B.Schemes := inferInstance
  let : PreservesLimitsOfShape WalkingCospan
      (BigFppfOver.toScheme B S hS) := by
    apply comp_preservesLimitsOfShape
  let : HasPullbacks (BigFppfOver B S hS) := inferInstance
  let : HasBinaryProducts (BigFppfOver B S hS) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  have hrepr : yoneda.relativelyRepresentable q :=
    (Functor.relativelyRepresentable.diag_iff (F := yoneda) (X := F)).mp
      hF.diagonal_representable q
  have hsurjPoints :=
    (surjective_iff_pointsMap_surjective B S hS
      (isAlgebraicSpace_yoneda B S hS U) hF q hrepr).mp hsurj
  refine ⟨hF, fun _ => isAlgebraicSpace_yoneda B S hS U, ?_, ?_⟩
  · intro _ T φ hφ
    let Q := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)
    let : MorphismProperty.IsStableUnderComposition
        (@Etale.{u} : MorphismProperty Scheme.{u}) :=
      ⟨fun a b ha hb => Etale.etale_comp b (f := a)⟩
    let : Q.IsStableUnderComposition :=
      MorphismProperty.IsStableUnderComposition.inverseImage _
    let : Q.presheaf.IsStableUnderComposition :=
      MorphismProperty.relative_isStableUnderComposition Q
    exact MorphismProperty.comp_mem Q.presheaf _ _ hφ het
  · rw [Set.eq_univ_iff_forall]
    intro x
    obtain ⟨y, hy⟩ := hsurjPoints x
    exact Set.mem_iUnion.mpr ⟨PUnit.unit, Set.mem_range.mpr ⟨y, hy⟩⟩

/-- Pulling back a base-change stable property along the structure functor to schemes is again
base-change stable. -/
private theorem isStableUnderBaseChange_inverseImage_toScheme
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange] :
    (P.inverseImage (BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange :=
  ⟨by
    intro _ _ _ _ _ _ _ _ hs hg
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := P)
      (hs.map (BigFppfOver.toScheme B S hS)) hg⟩

/-- An étale morphism of representable presheaves is sent to an étale morphism of schemes. -/
private theorem etale_map_of_isEtale_yoneda_map
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {V W : BigFppfOver B S hS} (φ : V ⟶ W) (h : IsEtale B S hS (yoneda.map φ)) :
    Etale ((BigFppfOver.toScheme B S hS).map φ) := by
  have := isStableUnderBaseChange_inverseImage_toScheme B S hS (@Etale.{u})
  apply (MorphismProperty.relative_map_iff (F := yoneda)
    (P := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).1
  have hid : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map (𝟙 V)) := by
    apply (MorphismProperty.relative_map_iff (F := yoneda)
      (P := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))).2
    show Etale ((BigFppfOver.toScheme B S hS).map (𝟙 V))
    infer_instance
  simpa using h V (𝟙 (yoneda.obj V)) hid

/-- Glueability of an algebraic space can be checked on all affine schemes
étale over it, or on one étale covering by affine schemes. -/
@[stacks 0F9P]
theorem exists_etaleCovering_iff_isGlueable
  {R : Type u} {R' : Type v} [CommRing R] [CommRing R']
  (g : R →+* R') (f : R)
  (_hglue : BeauvilleLaszlo.IsGlueingPair g f)
  (B : BigFppfSite.{u})
  (hX : B.Contains (Spec (.of R)))
  (Y : _root_.AlgebraicGeometry.AlgebraicSpaces B (Spec (.of R)) hX) :
  (∃ (I : Type (u + 1))
      (W : I → BigFppfOver B (Spec (.of R)) hX)
      (p : ∀ i, yoneda.obj (W i) ⟶ Y.1),
      IsEtaleCovering B (Spec (.of R)) hX
        (fun i ↦ yoneda.obj (W i)) p ∧
        ∀ i, IsAffine ((BigFppfOver.toScheme B (Spec (.of R)) hX).obj (W i)) ∧
          IsGlueableGlobalSections g f B hX (W i)) ↔
    IsGlueableAlgebraicSpace g f B hX Y := by
  let : Algebra R R' := g.toAlgebra
  constructor
  · rintro ⟨I, W₀, p₀, hcover, hlocal⟩
    intro W p hWaff hWetale
    classical
    have hpb := isEtaleCovering_pullback
      B (Spec (.of R)) hX p (isAlgebraicSpace_yoneda
        B (Spec (.of R)) hX W) (fun i => yoneda.obj (W₀ i)) p₀ hcover
    let G := BigFppfOver.toScheme B (Spec (.of R)) hX
    have := isStableUnderBaseChange_inverseImage_toScheme B (Spec (.of R)) hX (@Etale.{u})
    let : HasPullbacks B.Schemes := inferInstance
    let : PreservesLimitsOfShape WalkingCospan G := by
      apply comp_preservesLimitsOfShape
    let : HasPullbacks (BigFppfOver B (Spec (.of R)) hX) := inferInstance
    let : HasBinaryProducts (BigFppfOver B (Spec (.of R)) hX) :=
      hasBinaryProducts_of_hasTerminal_and_pullbacks _
    have hPshPb : HasPullbacks ((BigFppfOver B (Spec (.of R)) hX)ᵒᵖ ⥤ Type u) := by
      set_option synthInstance.maxHeartbeats 400000 in infer_instance
    have hPshPb' : ∀ {X₁ X₂ X₃ : (BigFppfOver B (Spec (.of R)) hX)ᵒᵖ ⥤ Type u}
        (f₁ : X₁ ⟶ X₃) (f₂ : X₂ ⟶ X₃), HasLimit (cospan f₁ f₂) :=
      fun _ _ => HasLimitsOfShape.has_limit _
    let Ppull (i : I) := pullback p (p₀ i)
    choose J X hZarCover hAtlas using fun i =>
      exists_zariski_cover_affine_etale_atlas B (Spec (.of R)) hX
        (Ppull i) (hpb.source_isAlgebraicSpace i)
    choose U q V hUaff hUsurj hUet hVaff hVbase using hAtlas
    have hOuter : ∀ i, IsEtaleCovering B (Spec (.of R)) hX
        (fun j => (X i j).toFunctor) (fun j => (X i j).ι) := fun i =>
      isEtaleCovering_of_isZariskiCover_subfunctor B (Spec (.of R)) hX
        (hpb.source_isAlgebraicSpace i) (X i) (hZarCover i)
    have hInner : ∀ i j, IsEtaleCovering B (Spec (.of R)) hX
        (fun _ : PUnit => yoneda.obj (U i j)) (fun _ => q i j) := fun i j =>
      isEtaleCovering_punit_of_surjective_etale B (Spec (.of R)) hX
        ((hZarCover i).1 j).1 (q i j) (hUsurj i j) (hUet i j)
    let K₁ : ∀ i, Type u := fun i => Σ j : J i, PUnit
    let U₁ : ∀ i, K₁ i → (BigFppfOver B (Spec (.of R)) hX)ᵒᵖ ⥤ Type u :=
      fun i ij => yoneda.obj (U i ij.1)
    let q₁ : ∀ i ij, U₁ i ij ⟶ Ppull i :=
      fun i ij => q i ij.1 ≫ (X i ij.1).ι
    have hRefined : ∀ i, IsEtaleCovering B (Spec (.of R)) hX
        (U₁ i) (q₁ i) := fun i =>
      isEtaleCovering_comp
        B (Spec (.of R)) hX (fun _ : J i => PUnit)
        (fun j => (X i j).toFunctor) (fun j => (X i j).ι)
        (fun j _ => yoneda.obj (U i j)) (fun j _ => q i j)
        (hOuter i) (hInner i)
    have hFinal := isEtaleCovering_comp
      B (Spec (.of R)) hX K₁ Ppull
      (fun i => pullback.fst p (p₀ i)) U₁ q₁ hpb hRefined
    let K := Σ i, K₁ i
    let chart (k : K) := U k.1 k.2.1
    let θ (k : K) : (yoneda.obj (chart k)) ⟶ yoneda.obj W :=
      q₁ k.1 k.2 ≫ pullback.fst p (p₀ k.1)
    let qChart (k : K) : chart k ⟶ W := yoneda.preimage (θ k)
    have hqChart (k : K) : yoneda.map (qChart k) = θ k := by
      simp [qChart]
    let hWalg := isAlgebraicSpace_yoneda B (Spec (.of R)) hX W
    let : TopologicalSpace (points B (Spec (.of R)) hX (yoneda.obj W)) :=
      pointTopology B (Spec (.of R)) hX (yoneda.obj W)
    let Qsurj := MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) G
    have : Qsurj.IsStableUnderBaseChange :=
      isStableUnderBaseChange_inverseImage_toScheme B (Spec (.of R)) hX (@Surjective.{u})
    have hQC : IsQuasiCompactSpace B (Spec (.of R)) hX (yoneda.obj W) := by
      refine ⟨W, 𝟙 (yoneda.obj W), ?_, ?_, ?_⟩
      · let : IsAffine (G.obj W) := hWaff
        exact Scheme.compactSpace_of_isAffine (G.obj W)
      · show Qsurj.presheaf (yoneda.map (𝟙 W))
        apply (MorphismProperty.relative_map_iff (F := yoneda) (P := Qsurj)).2
        show Surjective (G.map (𝟙 W))
        infer_instance
      · intro U φ hφ
        simpa using hφ
    let : CompactSpace (points B (Spec (.of R)) hX (yoneda.obj W)) :=
      (isQuasiCompactSpace_iff_compactSpace_points B (Spec (.of R)) hX
        (yoneda.obj W) hWalg).mp hQC
    have hOpen : ∀ k : K, IsOpen (Set.range
        (pointsMap B (Spec (.of R)) hX (yoneda.obj (chart k)) (θ k))) := by
      intro k
      let : TopologicalSpace (points B (Spec (.of R)) hX
          (yoneda.obj (chart k))) := pointTopology B (Spec (.of R)) hX
            (yoneda.obj (chart k))
      exact (isOpenMap_pointsMap_of_isEtale B (Spec (.of R)) hX (θ k)
        (hFinal.source_isAlgebraicSpace k) hWalg (hFinal.etale k)).isOpen_range
    have hCoverEq : (⋃ k : K, Set.range
        (pointsMap B (Spec (.of R)) hX (yoneda.obj (chart k)) (θ k))) =
          Set.univ := by
      simpa [K, chart, θ] using hFinal.jointly_surjective
    have hCover : Set.univ ⊆ ⋃ k : K, Set.range
        (pointsMap B (Spec (.of R)) hX (yoneda.obj (chart k)) (θ k)) := by
      rw [← hCoverEq]
    let O (k : K) : Set (points B (Spec (.of R)) hX (yoneda.obj W)) :=
      Set.range (pointsMap B (Spec (.of R)) hX (yoneda.obj (chart k)) (θ k))
    have hOopen : ∀ k, IsOpen (O k) := hOpen
    obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover O hOopen hCover
    let Wsp : _root_.AlgebraicGeometry.AlgebraicSpaces B (Spec (.of R)) hX :=
      ⟨yoneda.obj W, hWalg⟩
    let W0sp (i : I) : _root_.AlgebraicGeometry.AlgebraicSpaces B (Spec (.of R)) hX :=
      ⟨yoneda.obj (W₀ i), hcover.source_isAlgebraicSpace i⟩
    let psp : Wsp ⟶ Y := ObjectProperty.homMk p
    let p0sp (i : I) : W0sp i ⟶ Y := ObjectProperty.homMk (p₀ i)
    have hSndEtale (i : I) : IsEtale B (Spec (.of R)) hX
        (pullback.snd p (p₀ i)) := by
      let Psp := _root_.AlgebraicGeometry.AlgebraicSpaces.fiberProduct B (Spec (.of R)) hX
        psp (p0sp i)
      have hpbsp := _root_.AlgebraicGeometry.AlgebraicSpaces.isPullback_fiberProduct
        B (Spec (.of R)) hX psp (p0sp i)
      exact isEtale_of_isPullback B (Spec (.of R)) hX
        (ObjectProperty.homMk (pullback.fst p (p₀ i)) : Psp ⟶ Wsp)
        (ObjectProperty.homMk (pullback.snd p (p₀ i)) : Psp ⟶ W0sp i)
        psp (p0sp i) (by simpa [Psp, psp, p0sp] using hpbsp) hWetale
    let I' := ULift.{u} (Fin t.card)
    let eFin : (↑t : Type (u + 1)) ≃ Fin t.card := t.equivFin
    let sel (i : I') : K := (eFin.symm i.down).val
    let YI (i : I') : Scheme.{u} := G.obj (chart (sel i))
    let A : Scheme.{u} := ∐ YI
    have hAsmall : A.size < B.cutoff := by
      show (∐ YI).size < B.cutoff
      have hI : Cardinal.mk I' ≤ Cardinal.aleph0 := Cardinal.mk_le_aleph0
      exact Scheme.size_sigmaObj_lt B.aleph0_lt_cutoff B.aleph0_lt_cutoff_cof
        hI YI (fun i => (chart (sel i)).left.property)
    let a : A ⟶ G.obj W :=
      Limits.Sigma.desc (fun i : I' => G.map (qChart (sel i)))
    have hSigma (i : I') :
        Limits.Sigma.ι YI i ≫ a = G.map (qChart (sel i)) :=
      Limits.Sigma.ι_desc _ _
    let aSite : B.obj hAsmall ⟶ W.left := B.inclusion.preimage
      (show B.inclusion.obj (B.obj hAsmall) ⟶ B.inclusion.obj W.left from a)
    let V : BigFppfOver B (Spec (.of R)) hX := Over.mk (aSite ≫ W.hom)
    let q : V ⟶ W := Over.homMk aSite
    let viArrow (i : I') : (chart (sel i)).left ⟶ V.left :=
      B.inclusion.preimage
        (show B.inclusion.obj (chart (sel i)).left ⟶ B.inclusion.obj V.left from
          Sigma.ι YI i)
    have hmapq' : B.inclusion.map aSite = a := by
      rw [B.inclusion.map_preimage]
    have hmapq : G.map q = a := hmapq'
    have hviFac (i : I') : viArrow i ≫ aSite ≫ W.hom = (chart (sel i)).hom := by
      apply B.inclusion.map_injective
      rw [B.inclusion.map_comp, B.inclusion.map_comp,
        B.inclusion.map_preimage, B.inclusion.map_preimage]
      calc
        (Limits.Sigma.ι YI i ≫ a) ≫ B.inclusion.map W.hom =
            G.map (qChart (sel i)) ≫ B.inclusion.map W.hom := by rw [hSigma]
        _ = B.inclusion.map (chart (sel i)).hom := by
          show B.inclusion.map (qChart (sel i)).left ≫ B.inclusion.map W.hom = _
          rw [← B.inclusion.map_comp, (qChart (sel i)).w]
    let hvi (i : I') : chart (sel i) ⟶ V := Over.homMk (viArrow i) (hviFac i)
    have hmapvi (i : I') : B.inclusion.map (hvi i).left = Sigma.ι YI i := by
      show B.inclusion.map (viArrow i) = Sigma.ι YI i
      dsimp [viArrow]
      exact B.inclusion.map_preimage _
    have hvi_comp (i : I') : hvi i ≫ q = qChart (sel i) := by
      apply Over.OverMorphism.ext
      apply B.inclusion.map_injective
      show B.inclusion.map ((hvi i).left ≫ aSite) =
        B.inclusion.map (qChart (sel i)).left
      rw [B.inclusion.map_comp, hmapvi i, hmapq']
      show Limits.Sigma.ι YI i ≫ a = B.inclusion.map (qChart (sel i)).left
      exact hSigma i
    have hβsurj : Function.Surjective
        (pointsMap B (Spec (.of R)) hX (yoneda.obj V) (yoneda.map q)) := by
      intro x
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp (ht (Set.mem_univ x))
      obtain ⟨hkT, hmem⟩ := Set.mem_iUnion.mp hk
      obtain ⟨z, hz⟩ := Set.mem_range.mp hmem
      let i : I' := ULift.up (eFin ⟨k, hkT⟩)
      have hiSel : sel i = k := by simp [sel, i]
      let z' : points B (Spec (.of R)) hX
          (yoneda.obj (chart (sel i))) := hiSel.symm ▸ z
      refine ⟨pointsMap B (Spec (.of R)) hX
        (yoneda.obj (chart (sel i))) (yoneda.map (hvi i)) z', ?_⟩
      calc
        pointsMap B (Spec (.of R)) hX (yoneda.obj V) (yoneda.map q)
            (pointsMap B (Spec (.of R)) hX (yoneda.obj (chart (sel i)))
              (yoneda.map (hvi i)) z') =
          pointsMap B (Spec (.of R)) hX (yoneda.obj (chart (sel i)))
            (yoneda.map (hvi i) ≫ yoneda.map q) z' := by
              induction z' using Quot.inductionOn with
              | h r => simp only [pointsMap_class]; rfl
        _ = pointsMap B (Spec (.of R)) hX (yoneda.obj (chart (sel i)))
            (yoneda.map (qChart (sel i))) z' := by rw [← Functor.map_comp, hvi_comp]
        _ = x := by
          have hcast (k₁ k₂ : K) (h : k₁ = k₂)
              (z : points B (Spec (.of R)) hX (yoneda.obj (chart k₁))) :
              pointsMap B (Spec (.of R)) hX
                (yoneda.obj (chart k₂)) (yoneda.map (qChart k₂)) (h ▸ z) =
              pointsMap B (Spec (.of R)) hX
                (yoneda.obj (chart k₁)) (yoneda.map (qChart k₁)) z := by
            cases h
            rfl
          calc
            pointsMap B (Spec (.of R)) hX
                (yoneda.obj (chart (sel i))) (yoneda.map (qChart (sel i))) z' =
              pointsMap B (Spec (.of R)) hX
                (yoneda.obj (chart k)) (yoneda.map (qChart k)) z :=
                  hcast k (sel i) hiSel.symm z
            _ = pointsMap B (Spec (.of R)) hX
                (yoneda.obj (chart k)) (θ k) z := by rw [hqChart]
            _ = x := hz
    have hqSurj : Surjective (G.map q) :=
      (MorphismProperty.relative_map_iff (F := yoneda)
        (P := MorphismProperty.inverseImage
          (@Surjective.{u} : MorphismProperty Scheme.{u}) G)).1 <|
        (surjective_iff_surjective_pointsMap B (Spec (.of R)) hX
          (yoneda.obj W) hWalg V (yoneda.map q)).2 hβsurj
    let : ∀ i : I', IsAffine (YI i) := fun i => hUaff (sel i).1 (sel i).2.1
    let : IsAffine A := inferInstance
    let : IsAffine (G.obj V) := by change IsAffine A; infer_instance
    have hqFlat : Flat (G.map q) := by
      have hcompFlat (i : I') : Flat (G.map (qChart (sel i))) := by
        have : Etale (G.map (qChart (sel i))) :=
          etale_map_of_isEtale_yoneda_map B (Spec (.of R)) hX _
            (by rw [hqChart]; exact hFinal.etale (sel i))
        infer_instance
      have hdesc : Flat a := by
        let : HasRingHomProperty @Flat RingHom.Flat := inferInstance
        let : IsZariskiLocalAtSource @Flat :=
          HasRingHomProperty.instIsZariskiLocalAtSource (P := @Flat)
        show Flat (Sigma.desc (fun i : I' => G.map (qChart (sel i))))
        exact IsZariskiLocalAtSource.sigmaDesc (P := @Flat) hcompFlat
      rw [hmapq]
      exact hdesc
    have hff : (G.map q).appTop.hom.FaithfullyFlat :=
      (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine (G.map q)).mp
        ⟨hqFlat, hqSurj⟩
    let θ₀ (k : K) : (yoneda.obj (chart k)) ⟶ yoneda.obj (W₀ k.1) :=
      q₁ k.1 k.2 ≫ pullback.snd p (p₀ k.1)
    let qChart₀ (k : K) : chart k ⟶ W₀ k.1 := yoneda.preimage (θ₀ k)
    have hqChart₀ (k : K) : yoneda.map (qChart₀ k) = θ₀ k := by
      simp [qChart₀]
    have hEtale₀ (k : K) : IsEtale B (Spec (.of R)) hX (θ₀ k) :=
      isEtale_comp B (Spec (.of R)) hX ((hRefined k.1).etale k.2) (hSndEtale k.1)
    have hChartGlue (k : K) : IsGlueableGlobalSections g f B hX (chart k) := by
      have : Etale (G.map (qChart₀ k)) :=
        etale_map_of_isEtale_yoneda_map B (Spec (.of R)) hX _
          (by rw [hqChart₀]; exact hEtale₀ k)
      exact (isGlueableGlobalSections_of_flat_map g f B hX (W₀ k.1) (chart k)
        (qChart₀ k) (hlocal k.1).1 (hUaff k.1 k.2.1) inferInstance).1
        (hlocal k.1).2
    let Ai : I' → Type u := fun i => Γ(YI i, ⊤)
    let : ∀ i : I', CommRing (Ai i) := fun _ => inferInstance
    let : ∀ i : I', Algebra R (Ai i) := fun i =>
      (((Scheme.ΓSpecIso (.of R)).inv ≫
        (B.inclusion.map (chart (sel i)).hom).appTop).hom).toAlgebra
    have hlocalProd : ∀ i : I',
        BeauvilleLaszlo.IsGlueableFor (S := R') (Ai i) f := fun i => hChartGlue (sel i)
    let eR : Γ(A, ⊤) ≃+* (∀ i : I', Ai i) :=
      RingEquiv.ofBijective
        (RingHom.pi (fun i => (Sigma.ι YI i).appTop.hom))
        (sigma_global_sections_bijective YI)
    let : Algebra R Γ(G.obj V, ⊤) :=
      (((Scheme.ΓSpecIso (.of R)).inv ≫
        (B.inclusion.map V.hom).appTop).hom).toAlgebra
    let : Algebra R (∀ i : I', Ai i) :=
      (RingHom.pi (fun i => algebraMap R (Ai i))).toAlgebra
    let : Algebra Γ(G.obj V, ⊤) (∀ i : I', Ai i) := eR.toRingHom.toAlgebra
    have hsections (i : I') :
        (Sigma.ι YI i).appTop.hom.comp (B.inclusion.map V.hom).appTop.hom =
          (B.inclusion.map (chart (sel i)).hom).appTop.hom := by
      rw [← hmapvi i]
      have hh := congrArg (fun z => (B.inclusion.map z).appTop.hom) (hvi i).w
      simpa only [Functor.map_comp, Scheme.Hom.comp_appTop, CommRingCat.hom_comp]
        using hh
    have hcompat : (algebraMap R (∀ i : I', Ai i)) =
        (eR.toRingHom.comp (algebraMap R Γ(G.obj V, ⊤))) := by
      ext r i
      rw [RingHom.algebraMap_toAlgebra, RingHom.pi_apply,
        RingHom.comp_apply]
      show (algebraMap R (Ai i)) r =
        (Sigma.ι YI i).appTop.hom (algebraMap R Γ(G.obj V, ⊤) r)
      simpa only [RingHom.algebraMap_toAlgebra, CommRingCat.hom_comp,
        RingHom.comp_apply] using
        (congrArg (fun z : R →+* Ai i => z r)
          (congrArg (fun z => z.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
            (hsections i))).symm
    have hTower : IsScalarTower R Γ(G.obj V, ⊤) (∀ i : I', Ai i) :=
      IsScalarTower.of_algebraMap_eq' hcompat
    let : IsScalarTower R Γ(G.obj V, ⊤) (∀ i : I', Ai i) := hTower
    let : Module.FaithfullyFlat Γ(G.obj V, ⊤) (∀ i : I', Ai i) := by
      let : Module.FaithfullyFlat Γ(G.obj V, ⊤) Γ(G.obj V, ⊤) :=
        Module.FaithfullyFlat.self _
      let eAlg : Γ(G.obj V, ⊤) ≃ₐ[Γ(G.obj V, ⊤)] (∀ i : I', Ai i) :=
        AlgEquiv.ofRingEquiv (f := eR) (by
          intro x
          simp [RingHom.algebraMap_toAlgebra])
      exact Module.FaithfullyFlat.of_linearEquiv
        (R := Γ(G.obj V, ⊤)) (M := Γ(G.obj V, ⊤)) eAlg.toLinearEquiv.symm
    have hProd : BeauvilleLaszlo.IsGlueableFor (S := R') (∀ i : I', Ai i) f :=
      (isGlueableFor_pi_iff (R := R) (S := R') (I := I') (M := Ai) f).2 hlocalProd
    have hVGlue : IsGlueableGlobalSections g f B hX V := by
      show BeauvilleLaszlo.IsGlueableFor (S := R') Γ(G.obj V, ⊤) f
      exact (@isGlueableFor_iff_of_faithfullyFlat_algebra
        R R' (Γ(G.obj V, ⊤)) (∀ i : I', Ai i)
        inferInstance inferInstance inferInstance inferInstance inferInstance
        inferInstance inferInstance inferInstance hTower f inferInstance).mpr hProd
    exact (isGlueableGlobalSections_of_flat_map g f B hX W V q inferInstance inferInstance
      hqFlat).2 hff hVGlue
  · intro hglueable
    obtain ⟨I, X, hZarCover, hAtlas⟩ :=
      exists_zariski_cover_affine_etale_atlas B (Spec (.of R)) hX
        Y.1 Y.property
    choose U q V hUaff hUsurj hUet hVaff hVbase using hAtlas
    have hOuter : IsEtaleCovering B (Spec (.of R)) hX
        (fun i => (X i).toFunctor) (fun i => (X i).ι) :=
      isEtaleCovering_of_isZariskiCover_subfunctor B (Spec (.of R)) hX
        Y.property X hZarCover
    have hInner : ∀ i, IsEtaleCovering B (Spec (.of R)) hX
        (fun _ : PUnit => yoneda.obj (U i)) (fun _ => q i) := fun i =>
      isEtaleCovering_punit_of_surjective_etale B (Spec (.of R)) hX
        (hZarCover.1 i).1 (q i) (hUsurj i) (hUet i)
    let J : I → Type u := fun _ => PUnit
    let U' : ∀ i, J i → (BigFppfOver B (Spec (.of R)) hX)ᵒᵖ ⥤ Type u :=
      fun i _ => yoneda.obj (U i)
    let q' : ∀ i j, U' i j ⟶ (X i).toFunctor := fun i _ => q i
    have hFinal := isEtaleCovering_comp
      B (Spec (.of R)) hX J (fun i => (X i).toFunctor)
      (fun i => (X i).ι) U' q' hOuter hInner
    let K := ULift.{u + 1} (Σ i, J i)
    let W : K → BigFppfOver B (Spec (.of R)) hX :=
      fun ij => U ij.down.1
    let p : ∀ ij, yoneda.obj (W ij) ⟶ Y.1 :=
      fun ij => q ij.down.1 ≫ (X ij.down.1).ι
    have hCover : IsEtaleCovering B (Spec (.of R)) hX
        (fun ij => yoneda.obj (W ij)) p := by
      refine ⟨hFinal.target_isAlgebraicSpace,
        (fun ij => hFinal.source_isAlgebraicSpace ij.down),
        (fun ij => hFinal.etale ij.down), ?_⟩
      rw [Set.eq_univ_iff_forall]
      intro z
      have hz : z ∈ ⋃ ij : (Σ i, J i),
          Set.range (pointsMap B (Spec (.of R)) hX
            (yoneda.obj (U ij.1)) (q ij.1 ≫ (X ij.1).ι)) := by
        rw [hFinal.jointly_surjective]
        exact Set.mem_univ z
      obtain ⟨ij, hij⟩ := Set.mem_iUnion.mp hz
      obtain ⟨y, hy⟩ := Set.mem_range.mp hij
      exact Set.mem_iUnion.mpr ⟨ULift.up ij, Set.mem_range.mpr ⟨y, hy⟩⟩
    exact ⟨K, W, p, hCover, fun ij =>
      ⟨hUaff ij.down.1, hglueable (W ij) (p ij) (hUaff ij.down.1) (hCover.etale ij)⟩⟩

/-- **Glueability of global sections passes along a flat morphism of affine objects of the
site.** If `q : V ⟶ W` is a morphism of the big fppf site over `Spec R` between objects with
affine underlying schemes whose underlying morphism of schemes is flat, and the global sections
of `W` are glueable for `(R → R', f)`, then so are those of `V`: the global sections of `V` are
a flat algebra over those of `W`, and glueability is inherited by flat base change. -/
theorem isGlueableGlobalSections_of_flat
    {R : Type u} {R' : Type v} [CommRing R] [CommRing R']
    (g : R →+* R') (f : R) (B : BigFppfSite.{u}) (hX : B.Contains (Spec (.of R)))
    {V W : BigFppfOver B (Spec (.of R)) hX} (q : V ⟶ W)
    (hWaff : IsAffine ((BigFppfOver.toScheme B (Spec (.of R)) hX).obj W))
    (hVaff : IsAffine ((BigFppfOver.toScheme B (Spec (.of R)) hX).obj V))
    (hflat : Flat ((BigFppfOver.toScheme B (Spec (.of R)) hX).map q))
    (hW : IsGlueableGlobalSections g f B hX W) :
    IsGlueableGlobalSections g f B hX V :=
  (isGlueableGlobalSections_of_flat_map g f B hX W V q hWaff hVaff hflat).1 hW

end AlgebraicGeometry.Space

end
