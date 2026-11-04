module

public import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.EtaleComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.HomDescent

/-!
# Morphisms of quasi-coherent descent data, read on charts

Let `X` be an algebraic space over a scheme `S` and let `(f i : Y i ⟶ X)` be a family of
algebraic spaces étale over `X`, for instance a Zariski covering.  Along an étale morphism the
inverse image of modules of Stacks 03LU is restriction of sections, by Stacks 03LW, so a
morphism of the canonical descent data of Stacks 04W5 of two `𝒪_X`-modules is a family of maps
on sections over the charts of the members of the family.  This file is the calculus of those
readings, and it converts the pairwise condition of a morphism of descent data into a
compatibility of the readings over a chart of a pairwise fibre product `Y i ×_X Y j`.

## Main definitions

* `AlgebraicGeometry.Space.QuasiCoherentDescent.etaleSectInv` inverts the reading of sections of
  Stacks 03LW, and `.etaleSect₂` reads a section of an iterated inverse image over the twice
  composed chart.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.etaleForm` reads a morphism of inverse images
  along an étale morphism as a morphism of the étale restrictions.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.pairChart` is the chart of `Y i ×_X Y j`
  attached to a chart of `Y i`, a chart of `Y j` and a morphism of the induced charts of `X`,
  with `pairChartFst` and `pairChartSnd` its comparisons with the two given charts.

## Main results

* `AlgebraicGeometry.Space.QuasiCoherentDescent.etaleSect_map` and `.etaleSect_restrict`:
  reading sections commutes with the inverse image of a morphism of modules, and with
  restriction along a morphism of charts.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.map_eq_of_etaleForm_eq`: a morphism of modules
  whose étale restriction is the étale form of a morphism of inverse images has that morphism as
  its inverse image.  This is what identifies a glued morphism with a prescribed one.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.canonicalComparison_etaleSect`: granted the
  compatibility `ModulePullbackCompIsoEtaleRestriction`, the canonical comparison of Stacks 04W5
  is, on sections over a chart, the transport along the equality of the two composite charts.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.etaleForm_compat_of_comparison`: **the pairwise
  condition of a morphism of descent data, read on charts** — two morphisms of inverse images
  intertwined by the canonical comparison have étale forms intertwined by that transport.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.isEtale_pairLift`,
  `.postcomp_pairChartFst_comp` and `.isIso_pairChartFst`: the chart of a pairwise fibre product
  built from a morphism of charts of `X` is étale over it, its two comparisons factor that
  morphism, and the first of them is an isomorphism.

## Implementation notes

Every statement about sections is proved from a lemma in which the comparison isomorphism of
Stacks 03LW — or whichever isomorphism is in play — is an *abstract* natural isomorphism,
instantiated only afterwards: stated directly at the comparison, the elaborator and then the
kernel unfold the small étale ringed topos of an algebraic space, which does not terminate.  For
the same reason the sections of an étale restriction are written on the restriction rather than
on the composite chart, and the equality of composites is moved across by rewriting the goal
with a parametric lemma rather than by `simp` or by a definitional step.

The module universe is the universe of the structure rings, because
`AlgebraicGeometry.Space.modulePullback` exists only there.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 04W3](https://stacks.math.columbia.edu/tag/04W3)
* [Stacks Project, Tag 04W5](https://stacks.math.columbia.edu/tag/04W5)
* [Stacks Project, Tag 04W6](https://stacks.math.columbia.edu/tag/04W6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space.QuasiCoherentDescent

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {A C D : AlgebraicSpaces B S hS}

/-! ### Isomorphisms of modules read on sections -/

/-- Equal morphisms of modules agree on sections. -/
private theorem val_app_congr {X Y : Modules.{u, u} B S hS C.1 C.2} {φ ψ : X ⟶ Y}
    (h : φ = ψ) (U : SmallEtale B S hS C.1) (m : X.val.obj (.op U)) :
    φ.val.app (.op U) m = ψ.val.app (.op U) m :=
  h ▸ rfl

/-- A natural isomorphism of functors of modules, read on sections: its inverse undoes it. -/
theorem natIso_inv_hom_val_app
    {F G : Modules.{u, u} B S hS C.1 C.2 ⥤ Modules.{u, u} B S hS D.1 D.2} (e : F ≅ G)
    (M : Modules.{u, u} B S hS C.1 C.2) (U : SmallEtale B S hS D.1)
    (m : (F.obj M).val.obj (.op U)) :
    (e.inv.app M).val.app (.op U) ((e.hom.app M).val.app (.op U) m) = m :=
  val_app_congr B S hS (e.hom_inv_id_app M) U m

/-- A natural isomorphism of functors of modules, read on sections: it undoes its inverse. -/
theorem natIso_hom_inv_val_app
    {F G : Modules.{u, u} B S hS C.1 C.2 ⥤ Modules.{u, u} B S hS D.1 D.2} (e : F ≅ G)
    (M : Modules.{u, u} B S hS C.1 C.2) (U : SmallEtale B S hS D.1)
    (s : (G.obj M).val.obj (.op U)) :
    (e.hom.app M).val.app (.op U) ((e.inv.app M).val.app (.op U) s) = s :=
  val_app_congr B S hS (e.inv_hom_id_app M) U s

/-- A natural isomorphism of functors of modules, read on sections, is natural in the
module. -/
theorem natIso_hom_naturality_val_app
    {F G : Modules.{u, u} B S hS C.1 C.2 ⥤ Modules.{u, u} B S hS D.1 D.2} (e : F ≅ G)
    {M N : Modules.{u, u} B S hS C.1 C.2} (w : M ⟶ N) (U : SmallEtale B S hS D.1)
    (m : (F.obj M).val.obj (.op U)) :
    (e.hom.app N).val.app (.op U) ((F.map w).val.app (.op U) m) =
      ((G.map w).val.app (.op U)) ((e.hom.app M).val.app (.op U) m) :=
  val_app_congr B S hS (e.hom.naturality w) U m

/-! ### The calculus of readings of sections -/

/-- The reading of sections of Stacks 03LW, inverted: a section of the étale restriction read as
a section of the inverse image. -/
def etaleSectInv (g : D ⟶ C) (hg : IsEtale B S hS g.hom) (M : Modules.{u, u} B S hS C.1 C.2)
    (U : SmallEtale B S hS D.1)
    (s : ((etaleModulePullback.{u, u} B S hS g hg).obj M).val.obj (.op U)) :
    ((modulePullback B S hS g).obj M).val.obj (.op U) :=
  ((modulePullbackIsoEtaleModulePullback B S hS g hg).inv.app M).val.app (.op U) s

/-- Reading a section of an inverse image and reading it back is the identity. -/
theorem etaleSectInv_etaleSect (g : D ⟶ C) (hg : IsEtale B S hS g.hom)
    (M : Modules.{u, u} B S hS C.1 C.2) (U : SmallEtale B S hS D.1)
    (m : ((modulePullback B S hS g).obj M).val.obj (.op U)) :
    etaleSectInv B S hS g hg M U (etaleSect B S hS g hg M U m) = m := by
  simp only [etaleSect, etaleSectInv,
    natIso_inv_hom_val_app B S hS (modulePullbackIsoEtaleModulePullback B S hS g hg)]

/-- Reading a section of an étale restriction back and reading it again is the identity. -/
theorem etaleSect_etaleSectInv (g : D ⟶ C) (hg : IsEtale B S hS g.hom)
    (M : Modules.{u, u} B S hS C.1 C.2) (U : SmallEtale B S hS D.1)
    (s : ((etaleModulePullback.{u, u} B S hS g hg).obj M).val.obj (.op U)) :
    etaleSect B S hS g hg M U (etaleSectInv B S hS g hg M U s) = s := by
  simp only [etaleSect, etaleSectInv,
    natIso_hom_inv_val_app B S hS (modulePullbackIsoEtaleModulePullback B S hS g hg)]
  rfl

/-- Reading sections commutes with the inverse image of a morphism of modules. -/
theorem etaleSect_map (g : D ⟶ C) (hg : IsEtale B S hS g.hom)
    {M N : Modules.{u, u} B S hS C.1 C.2} (w : M ⟶ N) (U : SmallEtale B S hS D.1)
    (m : ((modulePullback B S hS g).obj M).val.obj (.op U)) :
    etaleSect B S hS g hg N U (((modulePullback B S hS g).map w).val.app (.op U) m) =
      w.val.app (.op ((smallEtalePostcomp B S hS g hg).obj U)) (etaleSect B S hS g hg M U m) := by
  simp only [etaleSect,
    natIso_hom_naturality_val_app B S hS (modulePullbackIsoEtaleModulePullback B S hS g hg) w]
  rfl

/-- Reading sections commutes with restriction along a morphism of charts. -/
theorem etaleSect_restrict (g : D ⟶ C) (hg : IsEtale B S hS g.hom)
    (M : Modules.{u, u} B S hS C.1 C.2) {U U' : SmallEtale B S hS D.1} (c : U' ⟶ U)
    (m : ((modulePullback B S hS g).obj M).val.obj (.op U)) :
    etaleSect B S hS g hg M U' (((modulePullback B S hS g).obj M).val.map c.op m) =
      M.val.map ((smallEtalePostcomp B S hS g hg).map c).op (etaleSect B S hS g hg M U m) :=
  PresheafOfModules.naturality_apply
    ((modulePullbackIsoEtaleModulePullback B S hS g hg).hom.app M).val c.op m

/-! ### The étale form of a morphism of inverse images -/

/-- A morphism of the inverse images of two modules along an étale morphism, read as a morphism
of their étale restrictions. -/
def etaleForm (g : D ⟶ C) (hg : IsEtale B S hS g.hom) {M N : Modules.{u, u} B S hS C.1 C.2}
    (w : (modulePullback B S hS g).obj M ⟶ (modulePullback B S hS g).obj N) :
    (etaleModulePullback.{u, u} B S hS g hg).obj M ⟶
      (etaleModulePullback.{u, u} B S hS g hg).obj N :=
  (modulePullbackIsoEtaleModulePullback B S hS g hg).inv.app M ≫ w ≫
    (modulePullbackIsoEtaleModulePullback B S hS g hg).hom.app N

/-- The comparison of Stacks 03LW carries a morphism of inverse images to its étale form. -/
theorem hom_comp_etaleForm (g : D ⟶ C) (hg : IsEtale B S hS g.hom)
    {M N : Modules.{u, u} B S hS C.1 C.2}
    (w : (modulePullback B S hS g).obj M ⟶ (modulePullback B S hS g).obj N) :
    (modulePullbackIsoEtaleModulePullback B S hS g hg).hom.app M ≫ etaleForm B S hS g hg w =
      w ≫ (modulePullbackIsoEtaleModulePullback B S hS g hg).hom.app N := by
  simp [etaleForm]

/-- A morphism of modules whose étale restriction is the étale form of a morphism of inverse
images has that morphism as its inverse image. -/
theorem map_eq_of_etaleForm_eq (g : D ⟶ C) (hg : IsEtale B S hS g.hom)
    {M N : Modules.{u, u} B S hS C.1 C.2} (φ : M ⟶ N)
    (w : (modulePullback B S hS g).obj M ⟶ (modulePullback B S hS g).obj N)
    (h : (etaleModulePullback.{u, u} B S hS g hg).map φ = etaleForm B S hS g hg w) :
    (modulePullback B S hS g).map φ = w := by
  have hnat := (modulePullbackIsoEtaleModulePullback B S hS g hg).hom.naturality φ
  rw [h, hom_comp_etaleForm B S hS g hg w] at hnat
  exact (cancel_mono ((modulePullbackIsoEtaleModulePullback B S hS g hg).hom.app N)).1 hnat

/-- A composite of morphisms of modules, read on sections. -/
theorem comp_val_app {X Y Z : Modules.{u, u} B S hS D.1 D.2} (x : X ⟶ Y) (y : Y ⟶ Z)
    (U : SmallEtale B S hS D.1) (m : X.val.obj (.op U)) :
    (x ≫ y).val.app (.op U) m = y.val.app (.op U) (x.val.app (.op U) m) :=
  rfl

/-- Reading sections of the étale form of a morphism of inverse images. -/
theorem etaleForm_val_app (g : D ⟶ C) (hg : IsEtale B S hS g.hom)
    {M N : Modules.{u, u} B S hS C.1 C.2}
    (w : (modulePullback B S hS g).obj M ⟶ (modulePullback B S hS g).obj N)
    (U : SmallEtale B S hS D.1)
    (m : ((modulePullback B S hS g).obj M).val.obj (.op U)) :
    (etaleForm B S hS g hg w).val.app (.op U) (etaleSect B S hS g hg M U m) =
      etaleSect B S hS g hg N U (w.val.app (.op U) m) := by
  simp only [etaleSect, etaleForm, comp_val_app,
    natIso_inv_hom_val_app B S hS (modulePullbackIsoEtaleModulePullback B S hS g hg)]

/-- A morphism of modules on the small étale site is natural in the chart. -/
theorem val_app_restrict {M' N' : Modules.{u, u} B S hS D.1 D.2} (φ : M' ⟶ N')
    {U U' : SmallEtale B S hS D.1} (c : U' ⟶ U) (t : M'.val.obj (.op U)) :
    φ.val.app (.op U') (M'.val.map c.op t) = N'.val.map c.op (φ.val.app (.op U) t) :=
  PresheafOfModules.naturality_apply φ.val c.op t

/-- Restriction of sections of a module along a composite of two morphisms of charts. -/
theorem val_map_comp {M' : Modules.{u, u} B S hS D.1 D.2}
    {U₁ U₂ U₃ : SmallEtale B S hS D.1} (c : U₁ ⟶ U₂) (d : U₂ ⟶ U₃)
    (t : M'.val.obj (.op U₃)) :
    M'.val.map c.op (M'.val.map d.op t) = M'.val.map (c ≫ d).op t :=
  (M'.val.map_comp_apply d.op c.op t).symm

/-! ### The canonical comparison of Stacks 04W5 on sections -/

section Comparison

variable {P Q R : AlgebraicSpaces B S hS}

/-- The reading of a section of an iterated inverse image along two étale morphisms, over a
chart, as a section over the twice composed chart. -/
def etaleSect₂ {P' Q' A' : AlgebraicSpaces B S hS} (c : P' ⟶ Q') (hc : IsEtale B S hS c.hom)
    (g : Q' ⟶ A') (hg : IsEtale B S hS g.hom) (M : Modules.{u, u} B S hS A'.1 A'.2)
    (U : SmallEtale B S hS P'.1)
    (y : ((modulePullback B S hS c).obj ((modulePullback B S hS g).obj M)).val.obj (.op U)) :
    M.val.obj (.op ((smallEtalePostcomp B S hS g hg).obj
      ((smallEtalePostcomp B S hS c hc).obj U))) :=
  etaleSect B S hS g hg M ((smallEtalePostcomp B S hS c hc).obj U)
    (etaleSect B S hS c hc ((modulePullback B S hS g).obj M) U y)

/-- A natural isomorphism read at a module, on sections. -/
theorem natIso_app_hom_val_app
    {F G : Modules.{u, u} B S hS A.1 A.2 ⥤ Modules.{u, u} B S hS P.1 P.2} (e : F ≅ G)
    (M : Modules.{u, u} B S hS A.1 A.2) (U : SmallEtale B S hS P.1)
    (m : (F.obj M).val.obj (.op U)) :
    ((e.app M).hom).val.app (.op U) m = (e.hom.app M).val.app (.op U) m :=
  rfl

/-- The inverse of a natural isomorphism read at a module, on sections. -/
theorem natIso_app_symm_hom_val_app
    {F G : Modules.{u, u} B S hS A.1 A.2 ⥤ Modules.{u, u} B S hS P.1 P.2} (e : F ≅ G)
    (M : Modules.{u, u} B S hS A.1 A.2) (U : SmallEtale B S hS P.1)
    (s : (G.obj M).val.obj (.op U)) :
    ((e.app M).symm.hom).val.app (.op U) s = (e.inv.app M).val.app (.op U) s :=
  rfl

/-- A transport along an equality of modules, on sections. -/
theorem eqToIso_hom_val_app {Z Z' : Modules.{u, u} B S hS P.1 P.2} (eq : Z = Z')
    (U : SmallEtale B S hS P.1) (m : Z.val.obj (.op U)) :
    ((eqToIso eq).hom).val.app (.op U) m = (eqToHom eq).val.app (.op U) m :=
  rfl

/-- **The canonical comparison of Stacks 04W5, read on sections over a chart.**  Granted the
compatibility of the comparison of Stacks 03LU with étale restriction, a section of an iterated
inverse image carried by the canonical comparison and read over the composite chart is that
section read over the other composite chart, transported along their equality. -/
theorem canonicalComparison_etaleSect
    (a : P ⟶ Q) (b : P ⟶ R)
    (fi : Q ⟶ A) (fj : R ⟶ A) (h : a ≫ fi = b ≫ fj) (ha : IsEtale B S hS a.hom)
    (hb : IsEtale B S hS b.hom) (hfi : IsEtale B S hS fi.hom) (hfj : IsEtale B S hS fj.hom)
    (hafi : IsEtale B S hS (a ≫ fi).hom) (hbfj : IsEtale B S hS (b ≫ fj).hom)
    (hca : EtaleRestrictionComp B S hS a fi ha hfi hafi)
    (hcb : EtaleRestrictionComp B S hS b fj hb hfj hbfj)
    (M : Modules.{u, u} B S hS A.1 A.2) (U : SmallEtale B S hS P.1)
    (m : ((modulePullback B S hS a).obj ((modulePullback B S hS fi).obj M)).val.obj (.op U)) :
    etaleSect B S hS fj hfj M ((smallEtalePostcomp B S hS b hb).obj U)
        (etaleSect B S hS b hb ((modulePullback B S hS fj).obj M) U
          ((canonicalComparison a b fi fj h M).hom.val.app (.op U) m)) =
      eqToHom (congrArg (fun V : SmallEtale B S hS A.1 => M.val.presheaf.obj (.op V))
          (smallEtalePostcomp_obj_congr B S hS hafi hbfj h U))
        (etaleSect B S hS fi hfi M ((smallEtalePostcomp B S hS a ha).obj U)
          (etaleSect B S hS a ha ((modulePullback B S hS fi).obj M) U m)) := by
  have step1 : (canonicalComparison a b fi fj h M).hom.val.app (.op U) m =
      (((modulePullbackCompIso B S hS a fi).app M ≪≫
          eqToIso (congrArg (fun r : P ⟶ A => (modulePullback B S hS r).obj M) h) ≪≫
          ((modulePullbackCompIso B S hS b fj).app M).symm).hom).val.app (.op U) m :=
    val_app_congr B S hS (congrArg Iso.hom (canonicalComparison_eq a b fi fj h M)) U m
  rw [step1, trans_hom_val_app, natIso_app_hom_val_app, eqToIso_hom_val_app,
    natIso_app_symm_hom_val_app]
  exact etaleSect_comparisonComposite B S hS a b fi fj h ha hb hfi hfj hafi hbfj hca hcb M U m

/-- Reading, over a chart, the inverse image along `a` of a morphism of inverse images carried
by the canonical comparison: it is the étale form of that morphism, transported along the
equality of the two composite charts. -/
theorem etaleSect_comparison_map_left
    (a : P ⟶ Q) (b : P ⟶ R)
    (fi : Q ⟶ A) (fj : R ⟶ A) (h : a ≫ fi = b ≫ fj) (ha : IsEtale B S hS a.hom)
    (hb : IsEtale B S hS b.hom) (hfi : IsEtale B S hS fi.hom) (hfj : IsEtale B S hS fj.hom)
    (hafi : IsEtale B S hS (a ≫ fi).hom) (hbfj : IsEtale B S hS (b ≫ fj).hom)
    (hca : EtaleRestrictionComp B S hS a fi ha hfi hafi)
    (hcb : EtaleRestrictionComp B S hS b fj hb hfj hbfj)
    {M N : Modules.{u, u} B S hS A.1 A.2}
    (w : (modulePullback B S hS fi).obj M ⟶ (modulePullback B S hS fi).obj N)
    (U : SmallEtale B S hS P.1)
    (x : ((modulePullback B S hS a).obj ((modulePullback B S hS fi).obj M)).val.obj (.op U)) :
    etaleSect₂ B S hS b hb fj hfj N U
        ((canonicalComparison a b fi fj h N).hom.val.app (.op U)
          (((modulePullback B S hS a).map w).val.app (.op U) x)) =
      eqToHom (congrArg (fun V : SmallEtale B S hS A.1 => N.val.presheaf.obj (.op V))
          (smallEtalePostcomp_obj_congr B S hS hafi hbfj h U))
        ((etaleForm B S hS fi hfi w).val.app (.op ((smallEtalePostcomp B S hS a ha).obj U))
          (etaleSect₂ B S hS a ha fi hfi M U x)) := by
  rw [etaleSect₂, etaleSect₂]
  rw [canonicalComparison_etaleSect B S hS a b fi fj h ha hb hfi hfj hafi hbfj hca hcb N U,
    etaleSect_map B S hS a ha w U x,
    ← etaleForm_val_app B S hS fi hfi w ((smallEtalePostcomp B S hS a ha).obj U)
      (etaleSect B S hS a ha ((modulePullback B S hS fi).obj M) U x)]

/-- Reading, over a chart, the inverse image along `b` of a morphism of inverse images after the
canonical comparison: it is the étale form of that morphism applied to the transport. -/
theorem etaleSect_comparison_map_right
    (a : P ⟶ Q) (b : P ⟶ R)
    (fi : Q ⟶ A) (fj : R ⟶ A) (h : a ≫ fi = b ≫ fj) (ha : IsEtale B S hS a.hom)
    (hb : IsEtale B S hS b.hom) (hfi : IsEtale B S hS fi.hom) (hfj : IsEtale B S hS fj.hom)
    (hafi : IsEtale B S hS (a ≫ fi).hom) (hbfj : IsEtale B S hS (b ≫ fj).hom)
    (hca : EtaleRestrictionComp B S hS a fi ha hfi hafi)
    (hcb : EtaleRestrictionComp B S hS b fj hb hfj hbfj)
    {M N : Modules.{u, u} B S hS A.1 A.2}
    (w : (modulePullback B S hS fj).obj M ⟶ (modulePullback B S hS fj).obj N)
    (U : SmallEtale B S hS P.1)
    (x : ((modulePullback B S hS a).obj ((modulePullback B S hS fi).obj M)).val.obj (.op U)) :
    etaleSect₂ B S hS b hb fj hfj N U
        (((modulePullback B S hS b).map w).val.app (.op U)
          ((canonicalComparison a b fi fj h M).hom.val.app (.op U) x)) =
      (etaleForm B S hS fj hfj w).val.app (.op ((smallEtalePostcomp B S hS b hb).obj U))
        (eqToHom (congrArg (fun V : SmallEtale B S hS A.1 => M.val.presheaf.obj (.op V))
            (smallEtalePostcomp_obj_congr B S hS hafi hbfj h U))
          (etaleSect₂ B S hS a ha fi hfi M U x)) := by
  rw [etaleSect₂, etaleSect₂]
  rw [etaleSect_map B S hS b hb w U
      ((canonicalComparison a b fi fj h M).hom.val.app (.op U) x),
    ← etaleForm_val_app B S hS fj hfj w ((smallEtalePostcomp B S hS b hb).obj U)
      (etaleSect B S hS b hb ((modulePullback B S hS fj).obj M) U
        ((canonicalComparison a b fi fj h M).hom.val.app (.op U) x)),
    canonicalComparison_etaleSect B S hS a b fi fj h ha hb hfi hfj hafi hbfj hca hcb M U]

/-- The pairwise condition of a descent datum, read on sections over a chart: the two
intertwinings agree elementwise. -/
theorem comparison_val_app_of_naturality (a : P ⟶ Q) (b : P ⟶ R) (fi : Q ⟶ A) (fj : R ⟶ A)
    (h : a ≫ fi = b ≫ fj) {M N : Modules.{u, u} B S hS A.1 A.2}
    (w₁ : (modulePullback B S hS fi).obj M ⟶ (modulePullback B S hS fi).obj N)
    (w₂ : (modulePullback B S hS fj).obj M ⟶ (modulePullback B S hS fj).obj N)
    (hw : (modulePullback B S hS a).map w₁ ≫ (canonicalComparison a b fi fj h N).hom =
      (canonicalComparison a b fi fj h M).hom ≫ (modulePullback B S hS b).map w₂)
    (U : SmallEtale B S hS P.1)
    (x : ((modulePullback B S hS a).obj ((modulePullback B S hS fi).obj M)).val.obj (.op U)) :
    (canonicalComparison a b fi fj h N).hom.val.app (.op U)
        (((modulePullback B S hS a).map w₁).val.app (.op U) x) =
      ((modulePullback B S hS b).map w₂).val.app (.op U)
        ((canonicalComparison a b fi fj h M).hom.val.app (.op U) x) := by
  rw [← comp_val_app, ← comp_val_app]
  exact val_app_congr B S hS hw U x

/-- **The pairwise condition of a descent datum, read as a compatibility of étale forms.**  Two
morphisms of inverse images whose intertwinings by the canonical comparison agree on sections
over a chart have étale forms intertwined by the transport along the equality of the two
composite charts. -/
theorem etaleForm_compat_of_comparison
    (a : P ⟶ Q) (b : P ⟶ R)
    (fi : Q ⟶ A) (fj : R ⟶ A) (h : a ≫ fi = b ≫ fj) (ha : IsEtale B S hS a.hom)
    (hb : IsEtale B S hS b.hom) (hfi : IsEtale B S hS fi.hom) (hfj : IsEtale B S hS fj.hom)
    (hafi : IsEtale B S hS (a ≫ fi).hom) (hbfj : IsEtale B S hS (b ≫ fj).hom)
    (hca : EtaleRestrictionComp B S hS a fi ha hfi hafi)
    (hcb : EtaleRestrictionComp B S hS b fj hb hfj hbfj)
    {M N : Modules.{u, u} B S hS A.1 A.2}
    (w₁ : (modulePullback B S hS fi).obj M ⟶ (modulePullback B S hS fi).obj N)
    (w₂ : (modulePullback B S hS fj).obj M ⟶ (modulePullback B S hS fj).obj N)
    (U : SmallEtale B S hS P.1)
    (x : ((modulePullback B S hS a).obj ((modulePullback B S hS fi).obj M)).val.obj (.op U))
    (hx : (canonicalComparison a b fi fj h N).hom.val.app (.op U)
        (((modulePullback B S hS a).map w₁).val.app (.op U) x) =
      ((modulePullback B S hS b).map w₂).val.app (.op U)
        ((canonicalComparison a b fi fj h M).hom.val.app (.op U) x)) :
    eqToHom (congrArg (fun V : SmallEtale B S hS A.1 => N.val.presheaf.obj (.op V))
          (smallEtalePostcomp_obj_congr B S hS hafi hbfj h U))
        ((etaleForm B S hS fi hfi w₁).val.app (.op ((smallEtalePostcomp B S hS a ha).obj U))
          (etaleSect₂ B S hS a ha fi hfi M U x)) =
      (etaleForm B S hS fj hfj w₂).val.app (.op ((smallEtalePostcomp B S hS b hb).obj U))
        (eqToHom (congrArg (fun V : SmallEtale B S hS A.1 => M.val.presheaf.obj (.op V))
            (smallEtalePostcomp_obj_congr B S hS hafi hbfj h U))
          (etaleSect₂ B S hS a ha fi hfi M U x)) :=
  ((etaleSect_comparison_map_left B S hS a b fi fj h ha hb hfi hfj hafi hbfj hca hcb
        w₁ U x).symm.trans
      (congrArg (etaleSect₂ B S hS b hb fj hfj N U) hx)).trans
    (etaleSect_comparison_map_right B S hS a b fi fj h ha hb hfi hfj hafi hbfj hca hcb w₂ U x)

end Comparison

/-! ### Charts of a pairwise fibre product -/

variable {I : Type v} {X : AlgebraicSpaces B S hS} (Yi : I → AlgebraicSpaces B S hS)
  (f : ∀ i, Yi i ⟶ X)

/-- The first projection of a pairwise fibre product of a family of étale morphisms is étale,
being a base change of another member. -/
theorem isEtale_pairFst (hf : ∀ i, IsEtale B S hS (f i).hom) (i j : I) :
    IsEtale B S hS (pairFst B S hS Yi f i j).hom :=
  isEtale_of_isPullback B S hS (pairSnd B S hS Yi f i j) (pairFst B S hS Yi f i j) (f j) (f i)
    (AlgebraicSpaces.isPullback_fiberProduct B S hS (f i) (f j)).flip (hf j)

/-- The second projection of a pairwise fibre product of a family of étale morphisms is
étale. -/
theorem isEtale_pairSnd (hf : ∀ i, IsEtale B S hS (f i).hom) (i j : I) :
    IsEtale B S hS (pairSnd B S hS Yi f i j).hom :=
  isEtale_of_isPullback B S hS (pairFst B S hS Yi f i j) (pairSnd B S hS Yi f i j) (f i) (f j)
    (AlgebraicSpaces.isPullback_fiberProduct B S hS (f i) (f j)) (hf i)

variable (hf : ∀ i, IsEtale B S hS (f i).hom)

/-- **The compatibility of Stacks 03LU with étale restriction at the pairs a family needs.**
The pairwise condition of Stacks 04W3 is read on charts through the comparison of Stacks 03LU
at the two projections of a pairwise fibre product composed with the two members, and at no
other pair; this bundles exactly those instances of
`AlgebraicGeometry.Space.QuasiCoherentDescent.EtaleRestrictionComp`.

It is implied by the coherence at every pair of étale morphisms of algebraic spaces, and also,
through
`AlgebraicGeometry.Space.QuasiCoherentDescent.pairEtaleRestrictionComp_of_representable`, by the
relative representability of the members of the family. -/
structure PairEtaleRestrictionComp : Prop where
  /-- The coherence at the first projection followed by the first member. -/
  fst : ∀ i j, EtaleRestrictionComp B S hS (pairFst B S hS Yi f i j) (f i)
    (isEtale_pairFst B S hS Yi f hf i j) (hf i)
    (isEtale_comp B S hS (isEtale_pairFst B S hS Yi f hf i j) (hf i))
  /-- The coherence at the second projection followed by the second member. -/
  snd : ∀ i j, EtaleRestrictionComp B S hS (pairSnd B S hS Yi f i j) (f j)
    (isEtale_pairSnd B S hS Yi f hf i j) (hf j)
    (isEtale_comp B S hS (isEtale_pairSnd B S hS Yi f hf i j) (hf j))

/-- The coherence at every pair gives the coherence at the pairs a family needs. -/
theorem ModulePullbackCompIsoEtaleRestriction.toPair
    (hcomp : ModulePullbackCompIsoEtaleRestriction B S hS) :
    PairEtaleRestrictionComp B S hS Yi f hf where
  fst i j :=
    ModulePullbackCompIsoEtaleRestriction.toComp B S hS hcomp
      (pairFst B S hS Yi f i j) (f i) _ _ _
  snd i j :=
    ModulePullbackCompIsoEtaleRestriction.toComp B S hS hcomp
      (pairSnd B S hS Yi f i j) (f j) _ _ _

/-- The two morphisms out of a chart of `Y i` given by a morphism of the induced charts of `X`
have equal composites to `X`. -/
theorem pairLift_condition {i j : I} (V : SmallEtale B S hS (Yi i).1)
    (V' : SmallEtale B S hS (Yi j).1)
    (k : (smallEtalePostcomp B S hS (f i) (hf i)).obj V ⟶
      (smallEtalePostcomp B S hS (f j) (hf j)).obj V') :
    V.1.hom ≫ (f i).hom = (yoneda.map k.hom.left ≫ V'.1.hom) ≫ (f j).hom := by
  have hw : yoneda.map k.hom.left ≫ (V'.1.hom ≫ (f j).hom) = V.1.hom ≫ (f i).hom :=
    CostructuredArrow.w k.hom
  exact hw.symm.trans (Category.assoc _ _ _).symm

/-- The morphism from a chart of `Y i` to the pairwise fibre product `Y i ×_X Y j` determined by
a morphism of the induced charts of `X`. -/
def pairLift {i j : I} (V : SmallEtale B S hS (Yi i).1) (V' : SmallEtale B S hS (Yi j).1)
    (k : (smallEtalePostcomp B S hS (f i) (hf i)).obj V ⟶
      (smallEtalePostcomp B S hS (f j) (hf j)).obj V') :
    yoneda.obj V.1.left ⟶ (pair B S hS Yi f i j).1 :=
  pullback.lift V.1.hom (yoneda.map k.hom.left ≫ V'.1.hom)
    (pairLift_condition B S hS Yi f hf V V' k)

/-- The morphism to the pairwise fibre product composed with the first projection is the
structure morphism of the chart of `Y i`. -/
theorem pairLift_fst {i j : I} (V : SmallEtale B S hS (Yi i).1)
    (V' : SmallEtale B S hS (Yi j).1)
    (k : (smallEtalePostcomp B S hS (f i) (hf i)).obj V ⟶
      (smallEtalePostcomp B S hS (f j) (hf j)).obj V') :
    pairLift B S hS Yi f hf V V' k ≫ (pairFst B S hS Yi f i j).hom = V.1.hom :=
  pullback.lift_fst _ _ _

/-- The morphism to the pairwise fibre product composed with the second projection is the
chart morphism followed by the structure morphism of the chart of `Y j`. -/
theorem pairLift_snd {i j : I} (V : SmallEtale B S hS (Yi i).1)
    (V' : SmallEtale B S hS (Yi j).1)
    (k : (smallEtalePostcomp B S hS (f i) (hf i)).obj V ⟶
      (smallEtalePostcomp B S hS (f j) (hf j)).obj V') :
    pairLift B S hS Yi f hf V V' k ≫ (pairSnd B S hS Yi f i j).hom =
      yoneda.map k.hom.left ≫ V'.1.hom :=
  pullback.lift_snd _ _ _

/-- The morphism to the pairwise fibre product is étale, by cancellation between two morphisms
étale over `X`. -/
theorem isEtale_pairLift {i j : I} (V : SmallEtale B S hS (Yi i).1)
    (V' : SmallEtale B S hS (Yi j).1)
    (k : (smallEtalePostcomp B S hS (f i) (hf i)).obj V ⟶
      (smallEtalePostcomp B S hS (f j) (hf j)).obj V') :
    IsEtale B S hS (pairLift B S hS Yi f hf V V' k) :=
  isEtale_of_isEtale_over B S hS (isAlgebraicSpace_yoneda B S hS V.1.left)
    (pair B S hS Yi f i j).2 X.2 (pairLift B S hS Yi f hf V V' k) (V.1.hom ≫ (f i).hom)
    ((pairFst B S hS Yi f i j).hom ≫ (f i).hom)
    (isEtale_comp B S hS ((isEtale_iff_presheaf_of_yoneda B S hS V.1.hom).2 V.2) (hf i))
    (isEtale_comp B S hS (isEtale_pairFst B S hS Yi f hf i j) (hf i))
    (by rw [← Category.assoc, pairLift_fst])

/-- The chart of the pairwise fibre product `Y i ×_X Y j` determined by a chart `V` of `Y i`,
a chart `V'` of `Y j` and a morphism of the induced charts of `X`. -/
def pairChart {i j : I} (V : SmallEtale B S hS (Yi i).1) (V' : SmallEtale B S hS (Yi j).1)
    (k : (smallEtalePostcomp B S hS (f i) (hf i)).obj V ⟶
      (smallEtalePostcomp B S hS (f j) (hf j)).obj V') :
    SmallEtale B S hS (pair B S hS Yi f i j).1 :=
  ⟨CostructuredArrow.mk (pairLift B S hS Yi f hf V V' k),
    (isEtale_iff_presheaf_of_yoneda B S hS _).1 (isEtale_pairLift B S hS Yi f hf V V' k)⟩

/-- The chart of the pairwise fibre product maps to the chart of `Y i` it was built from. -/
def pairChartFst {i j : I} (V : SmallEtale B S hS (Yi i).1)
    (V' : SmallEtale B S hS (Yi j).1)
    (k : (smallEtalePostcomp B S hS (f i) (hf i)).obj V ⟶
      (smallEtalePostcomp B S hS (f j) (hf j)).obj V') :
    (smallEtalePostcomp B S hS (pairFst B S hS Yi f i j)
        (isEtale_pairFst B S hS Yi f hf i j)).obj (pairChart B S hS Yi f hf V V' k) ⟶ V :=
  ObjectProperty.homMk (CostructuredArrow.homMk (𝟙 V.1.left)
    (((congrArg (fun t => t ≫ V.1.hom) (yoneda.map_id V.1.left)).trans
        (Category.id_comp V.1.hom)).trans (pairLift_fst B S hS Yi f hf V V' k).symm))

/-- The chart of the pairwise fibre product maps to the chart of `Y j` it was built from. -/
def pairChartSnd {i j : I} (V : SmallEtale B S hS (Yi i).1)
    (V' : SmallEtale B S hS (Yi j).1)
    (k : (smallEtalePostcomp B S hS (f i) (hf i)).obj V ⟶
      (smallEtalePostcomp B S hS (f j) (hf j)).obj V') :
    (smallEtalePostcomp B S hS (pairSnd B S hS Yi f i j)
        (isEtale_pairSnd B S hS Yi f hf i j)).obj (pairChart B S hS Yi f hf V V' k) ⟶ V' :=
  ObjectProperty.homMk (CostructuredArrow.homMk k.hom.left
    (pairLift_snd B S hS Yi f hf V V' k).symm)

/-- The chart of `Y i` obtained from the chart of the pairwise fibre product by the first
projection. -/
abbrev pairObjFst {i j : I} (V : SmallEtale B S hS (Yi i).1)
    (V' : SmallEtale B S hS (Yi j).1)
    (k : (smallEtalePostcomp B S hS (f i) (hf i)).obj V ⟶
      (smallEtalePostcomp B S hS (f j) (hf j)).obj V') : SmallEtale B S hS (Yi i).1 :=
  (smallEtalePostcomp B S hS (pairFst B S hS Yi f i j)
    (isEtale_pairFst B S hS Yi f hf i j)).obj (pairChart B S hS Yi f hf V V' k)

/-- The chart of `Y j` obtained from the chart of the pairwise fibre product by the second
projection. -/
abbrev pairObjSnd {i j : I} (V : SmallEtale B S hS (Yi i).1)
    (V' : SmallEtale B S hS (Yi j).1)
    (k : (smallEtalePostcomp B S hS (f i) (hf i)).obj V ⟶
      (smallEtalePostcomp B S hS (f j) (hf j)).obj V') : SmallEtale B S hS (Yi j).1 :=
  (smallEtalePostcomp B S hS (pairSnd B S hS Yi f i j)
    (isEtale_pairSnd B S hS Yi f hf i j)).obj (pairChart B S hS Yi f hf V V' k)

/-- The underlying morphism of the transport along an equality of charts. -/
theorem eqToHom_hom_left {A₁ A₂ : SmallEtale B S hS X.1} (e : A₁ = A₂) :
    (eqToHom e).hom.left =
      eqToHom (congrArg (fun Z : SmallEtale B S hS X.1 => Z.1.left) e) := by
  subst e
  rfl

/-- The underlying morphism of a transport along an equality of charts, followed by a morphism
of charts. -/
theorem eqToHom_comp_hom_left {A₁ A₂ A₃ : SmallEtale B S hS X.1} (e : A₁ = A₂) (c : A₂ ⟶ A₃) :
    (eqToHom e ≫ c).hom.left =
      eqToHom (congrArg (fun Z : SmallEtale B S hS X.1 => Z.1.left) e) ≫ c.hom.left := by
  subst e
  rfl

/-- The chart of `X` under the first projection and the one under the second projection, of the
chart of the pairwise fibre product, are equal: the two composites to `X` agree. -/
theorem postcomp_pairChart_eq {i j : I} (V : SmallEtale B S hS (Yi i).1)
    (V' : SmallEtale B S hS (Yi j).1)
    (k : (smallEtalePostcomp B S hS (f i) (hf i)).obj V ⟶
      (smallEtalePostcomp B S hS (f j) (hf j)).obj V') :
    (smallEtalePostcomp B S hS (f i) (hf i)).obj
        ((smallEtalePostcomp B S hS (pairFst B S hS Yi f i j)
          (isEtale_pairFst B S hS Yi f hf i j)).obj (pairChart B S hS Yi f hf V V' k)) =
      (smallEtalePostcomp B S hS (f j) (hf j)).obj
        ((smallEtalePostcomp B S hS (pairSnd B S hS Yi f i j)
          (isEtale_pairSnd B S hS Yi f hf i j)).obj (pairChart B S hS Yi f hf V V' k)) :=
  smallEtalePostcomp_obj_congr B S hS
    (isEtale_comp B S hS (isEtale_pairFst B S hS Yi f hf i j) (hf i))
    (isEtale_comp B S hS (isEtale_pairSnd B S hS Yi f hf i j) (hf j))
    (pair_condition B S hS Yi f i j) (pairChart B S hS Yi f hf V V' k)

/-- The morphism of charts of `X` out of the chart of the pairwise fibre product factors the
given morphism `k` in the two ways the two projections provide. -/
theorem postcomp_pairChartFst_comp {i j : I} (V : SmallEtale B S hS (Yi i).1)
    (V' : SmallEtale B S hS (Yi j).1)
    (k : (smallEtalePostcomp B S hS (f i) (hf i)).obj V ⟶
      (smallEtalePostcomp B S hS (f j) (hf j)).obj V') :
    (smallEtalePostcomp B S hS (f i) (hf i)).map (pairChartFst B S hS Yi f hf V V' k) ≫ k =
      eqToHom (postcomp_pairChart_eq B S hS Yi f hf V V' k) ≫
        (smallEtalePostcomp B S hS (f j) (hf j)).map
          (pairChartSnd B S hS Yi f hf V V' k) := by
  apply ObjectProperty.hom_ext
  apply CostructuredArrow.hom_ext
  rw [eqToHom_comp_hom_left]
  rfl

/-- The chart of `Y i` under the first projection of the chart of the pairwise fibre product is
isomorphic to the chart it was built from, by the identity on underlying objects. -/
instance isIso_pairChartFst {i j : I} (V : SmallEtale B S hS (Yi i).1)
    (V' : SmallEtale B S hS (Yi j).1)
    (k : (smallEtalePostcomp B S hS (f i) (hf i)).obj V ⟶
      (smallEtalePostcomp B S hS (f j) (hf j)).obj V') :
    IsIso (pairChartFst B S hS Yi f hf V V' k) := by
  refine ⟨ObjectProperty.homMk (CostructuredArrow.homMk (𝟙 V.1.left)
    (((congrArg (fun t => t ≫ (pairLift B S hS Yi f hf V V' k ≫
          (pairFst B S hS Yi f i j).hom)) (yoneda.map_id V.1.left)).trans
        (Category.id_comp _)).trans (pairLift_fst B S hS Yi f hf V V' k))), ?_, ?_⟩ <;>
    apply ObjectProperty.hom_ext <;> apply CostructuredArrow.hom_ext <;>
    exact Category.id_comp _

/-- Restriction of sections along an identity of charts is the identity. -/
private theorem val_map_id_apply (M : Modules.{u, u} B S hS X.1 X.2) {V : SmallEtale B S hS X.1}
    (t : M.val.obj (.op V)) : M.val.map (𝟙 (.op V)) t = t :=
  CategoryTheory.congr_fun (M.val.map_id (.op V)) t

/-- Transport of sections along an equality of charts is restriction along the corresponding
morphism. -/
theorem val_map_eqToHom {V₁ V₂ : SmallEtale B S hS X.1} (e : V₁ = V₂)
    (M : Modules.{u, u} B S hS X.1 X.2) (t : M.val.obj (.op V₁)) :
    M.val.map (eqToHom e.symm).op t =
      eqToHom (congrArg (fun V : SmallEtale B S hS X.1 => M.val.presheaf.obj (.op V)) e) t := by
  subst e
  simp only [eqToHom_refl, op_id]
  exact val_map_id_apply B S hS M t

/-- Transport of sections along an equality of charts undoes restriction along it. -/
theorem val_map_eqToHom_eqToHom {V₁ V₂ : SmallEtale B S hS X.1} (e : V₁ = V₂)
    (M : Modules.{u, u} B S hS X.1 X.2) (t : M.val.obj (.op V₂)) :
    eqToHom (congrArg (fun V : SmallEtale B S hS X.1 => M.val.presheaf.obj (.op V)) e)
        (M.val.map (eqToHom e).op t) = t := by
  subst e
  simp only [eqToHom_refl, op_id]
  exact val_map_id_apply B S hS M t

/-- Restriction of sections along an equality of charts undoes the transport along it. -/
theorem eqToHom_val_map_eqToHom {V₁ V₂ : SmallEtale B S hS X.1} (e : V₁ = V₂)
    (M : Modules.{u, u} B S hS X.1 X.2) (t : M.val.obj (.op V₁)) :
    M.val.map (eqToHom e).op
        (eqToHom (congrArg (fun V : SmallEtale B S hS X.1 => M.val.presheaf.obj (.op V)) e) t) =
      t := by
  subst e
  simp only [eqToHom_refl, op_id]
  exact val_map_id_apply B S hS M t


end AlgebraicGeometry.Space.QuasiCoherentDescent

end
