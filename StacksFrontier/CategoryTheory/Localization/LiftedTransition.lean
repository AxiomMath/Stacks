module

public import Mathlib.CategoryTheory.Localization.Predicate

/-!
# Transitions between derived functors assembled from a transition upstairs

Let `q : H ⥤ D` be a localization functor, let `F : D ⥤ Dl` be a functor lifting `Fh : H ⥤ Hl`
through localizations `q` and `ql`, let `G : Dl ⥤ Dn` be a functor equipped only with a
*comparison* `ql ⋙ G ⟶ Gh ⋙ qn` — the shape in which a total left derived functor comes — and
let `K : D ⥤ Dn` lift `Kh : H ⥤ Hn`. A natural transformation `Fh ⋙ Gh ⟶ Kh` upstairs then
produces a natural transformation `F ⋙ G ⟶ K` downstairs, and a cocycle condition upstairs
produces the corresponding cocycle condition downstairs.

## Main definitions

* `CategoryTheory.liftedTransitionComparison`: the whiskered composite
  `q ⋙ (F ⋙ G) ⟶ q ⋙ K` built from the two lifting isomorphisms, the comparison of `G` and the
  transformation upstairs.
* `CategoryTheory.liftedTransition`: its lift `F ⋙ G ⟶ K` along the localization `q`.

## Main results

* `CategoryTheory.liftedTransitionComparison_app` and
  `CategoryTheory.liftedTransition_app_q`: the two transformations read at an object.
* `CategoryTheory.isIso_liftedTransition`: the lifted transition is invertible as soon as the
  comparison of `G` and the transformation upstairs are.
* `CategoryTheory.liftedTransition_cocycle`: the cocycle condition for three lifted
  transitions, from the cocycle condition upstairs and the compatibility of the comparison of a
  composite of two functors `G` with the comparisons of the factors.

## Implementation notes

Everything here is stated at free variables. At the functors a consumer actually has — a
derived pullback and a derived restriction, each of them a composite of several layers of
sheaf-theoretic constructions — the unifier is forced to unfold those layers while matching the
associativity of whiskered composites, and that exhausts its heartbeats; at free variables
there is nothing to unfold, naturality of the composite of whiskerings is free, and the two
`app` formulas are immediate. The consumer then applies these results and never unfolds them.

The functors are implicit and the transformations between them explicit, so that a consumer
supplies only the comparisons: each of them determines the functors it compares.

The comparison `cmp : ql ⋙ G ⟶ Gh ⋙ qn` is deliberately not assumed invertible: for a total
left derived functor it is the canonical map out of the localization of the underived functor,
and its invertibility is a separate theorem. Only `F` and `K` are assumed to lift, which they
do when they are induced by exact functors.
-/

@[expose] public section

namespace CategoryTheory

open CategoryTheory

variable {H : Type*} [Category* H] {D : Type*} [Category* D]
  {Hl : Type*} [Category* Hl] {Dl : Type*} [Category* Dl]
  {Hm : Type*} [Category* Hm] {Dm : Type*} [Category* Dm]
  {Hn : Type*} [Category* Hn] {Dn : Type*} [Category* Dn]

section Comparison

variable {q : H ⥤ D} {ql : Hl ⥤ Dl} {qn : Hn ⥤ Dn}
  {F : D ⥤ Dl} {Fh : H ⥤ Hl} (e₁ : q ⋙ F ≅ Fh ⋙ ql)
  {G : Dl ⥤ Dn} {Gh : Hl ⥤ Hn} (cmp : ql ⋙ G ⟶ Gh ⋙ qn)
  {K : D ⥤ Dn} {Kh : H ⥤ Hn} (e₂ : q ⋙ K ≅ Kh ⋙ qn)
  (τ : Fh ⋙ Gh ⟶ Kh)

/-- The transformation `q ⋙ (F ⋙ G) ⟶ q ⋙ K` assembled from a transformation
`τ : Fh ⋙ Gh ⟶ Kh` upstairs: the lifting isomorphism of `F`, pushed forward by `G`; the
comparison of `G`; the localization of `τ`; and the inverse of the lifting isomorphism of
`K`. -/
def liftedTransitionComparison : q ⋙ F ⋙ G ⟶ q ⋙ K :=
  Functor.whiskerRight e₁.hom G ≫ Functor.whiskerLeft Fh cmp ≫
    Functor.whiskerRight τ qn ≫ e₂.inv

/-- The component of `liftedTransitionComparison` at an object `X` is the composite of the image
under `G` of the lifting isomorphism of `F`, the comparison of `G`, the image under `qn` of `τ`,
and the inverse of the lifting isomorphism of `K`, all at `X`. -/
@[simp]
theorem liftedTransitionComparison_app (X : H) :
    (liftedTransitionComparison e₁ cmp e₂ τ).app X =
      G.map (e₁.hom.app X) ≫ cmp.app (Fh.obj X) ≫ qn.map (τ.app X) ≫ e₂.inv.app X := by
  simp [liftedTransitionComparison]

variable (W : MorphismProperty H) [q.IsLocalization W]

/-- The transformation `F ⋙ G ⟶ K` obtained from a transformation `τ : Fh ⋙ Gh ⟶ Kh`
upstairs, by lifting `liftedTransitionComparison` along the localization `q`. -/
noncomputable def liftedTransition : F ⋙ G ⟶ K :=
  letI : Localization.Lifting q W (q ⋙ (F ⋙ G)) (F ⋙ G) := Localization.Lifting.compLeft q W _
  letI : Localization.Lifting q W (q ⋙ K) K := Localization.Lifting.compLeft q W _
  Localization.liftNatTrans q W (q ⋙ (F ⋙ G)) (q ⋙ K) (F ⋙ G) K
    (liftedTransitionComparison e₁ cmp e₂ τ)

/-- The component of `liftedTransition` at `q.obj X` is the composite of the image under `G` of
the lifting isomorphism of `F`, the comparison of `G`, the image under `qn` of `τ`, and the
inverse of the lifting isomorphism of `K`, all at `X`. -/
theorem liftedTransition_app_q (X : H) :
    (liftedTransition e₁ cmp e₂ τ W).app (q.obj X) =
      G.map (e₁.hom.app X) ≫ cmp.app (Fh.obj X) ≫ qn.map (τ.app X) ≫ e₂.inv.app X := by
  let _ : Localization.Lifting q W (q ⋙ (F ⋙ G)) (F ⋙ G) := Localization.Lifting.compLeft q W _
  let _ : Localization.Lifting q W (q ⋙ K) K := Localization.Lifting.compLeft q W _
  rw [liftedTransition, Localization.liftNatTrans_app]
  simp

/-- The lifted transition is invertible as soon as the comparison of `G` and the transformation
upstairs are. -/
theorem isIso_liftedTransition [IsIso cmp] [IsIso τ] :
    IsIso (liftedTransition e₁ cmp e₂ τ W) := by
  have := Localization.essSurj q W
  rw [NatTrans.isIso_iff_isIso_app]
  intro Z
  rw [NatTrans.isIso_app_iff_of_iso _ (q.objObjPreimageIso Z).symm, liftedTransition_app_q]
  infer_instance

end Comparison

section Cocycle

variable {q : H ⥤ D} {ql : Hl ⥤ Dl} {qm : Hm ⥤ Dm} {qn : Hn ⥤ Dn}
  {Fl : D ⥤ Dl} {Flh : H ⥤ Hl} (el : q ⋙ Fl ≅ Flh ⋙ ql)
  {Fm : D ⥤ Dm} {Fmh : H ⥤ Hm} (em : q ⋙ Fm ≅ Fmh ⋙ qm)
  {Fn : D ⥤ Dn} {Fnh : H ⥤ Hn} (en : q ⋙ Fn ≅ Fnh ⋙ qn)
  {Gψ : Dl ⥤ Dm} {Gψh : Hl ⥤ Hm} (cψ : ql ⋙ Gψ ⟶ Gψh ⋙ qm)
  {Gφ : Dm ⥤ Dn} {Gφh : Hm ⥤ Hn} (cφ : qm ⋙ Gφ ⟶ Gφh ⋙ qn)
  {Gχ : Dl ⥤ Dn} {Gχh : Hl ⥤ Hn} (cχ : ql ⋙ Gχ ⟶ Gχh ⋙ qn)
  (cmp : Gψ ⋙ Gφ ⟶ Gχ) (cmph : Gψh ⋙ Gφh ⟶ Gχh)
  (τψ : Flh ⋙ Gψh ⟶ Fmh) (τφ : Fmh ⋙ Gφh ⟶ Fnh) (τχ : Flh ⋙ Gχh ⟶ Fnh)

/-- The cocycle condition for the three comparisons of
`CategoryTheory.liftedTransitionComparison`, from the cocycle condition upstairs and the
factorization of the comparison of the composite through the comparisons of the factors. -/
theorem liftedTransitionComparison_cocycle
    (fac : ∀ Y : Hl, cmp.app (ql.obj Y) ≫ cχ.app Y =
      Gφ.map (cψ.app Y) ≫ cφ.app (Gψh.obj Y) ≫ qn.map (cmph.app Y))
    (cocycle : ∀ X : H, cmph.app (Flh.obj X) ≫ τχ.app X =
      Gφh.map (τψ.app X) ≫ τφ.app X)
    (X : H) :
    cmp.app (Fl.obj (q.obj X)) ≫ (liftedTransitionComparison el cχ en τχ).app X =
      Gφ.map ((liftedTransitionComparison el cψ em τψ).app X) ≫
        (liftedTransitionComparison em cφ en τφ).app X := by
  have hnat : ∀ {Z : Dn} (g : Gχ.obj (ql.obj (Flh.obj X)) ⟶ Z),
      cmp.app (Fl.obj (q.obj X)) ≫ Gχ.map (el.hom.app X) ≫ g =
        Gφ.map (Gψ.map (el.hom.app X)) ≫ cmp.app (ql.obj (Flh.obj X)) ≫ g := by
    intro Z g
    rw [← Category.assoc, ← Category.assoc]
    exact congrArg (fun t => t ≫ g) (cmp.naturality (el.hom.app X)).symm
  have hfac : ∀ {Z : Dn} (g : qn.obj (Gχh.obj (Flh.obj X)) ⟶ Z),
      cmp.app (ql.obj (Flh.obj X)) ≫ cχ.app (Flh.obj X) ≫ g =
        Gφ.map (cψ.app (Flh.obj X)) ≫
          cφ.app (Gψh.obj (Flh.obj X)) ≫ qn.map (cmph.app (Flh.obj X)) ≫ g := by
    intro Z g
    rw [← Category.assoc, fac (Flh.obj X), Category.assoc, Category.assoc]
  have hcφ : ∀ {Z : Dn} (g : qn.obj (Gφh.obj (Fmh.obj X)) ⟶ Z),
      Gφ.map (qm.map (τψ.app X)) ≫ cφ.app (Fmh.obj X) ≫ g =
        cφ.app (Gψh.obj (Flh.obj X)) ≫ qn.map (Gφh.map (τψ.app X)) ≫ g := by
    intro Z g
    rw [← Category.assoc, ← Category.assoc]
    exact congrArg (fun t => t ≫ g) (cφ.naturality (τψ.app X))
  rw [liftedTransitionComparison_app, liftedTransitionComparison_app,
    liftedTransitionComparison_app]
  simp only [Functor.map_comp, Category.assoc]
  rw [hnat, hfac, ← Functor.map_comp_assoc qn, cocycle X, Functor.map_comp_assoc qn,
    ← Functor.map_comp_assoc Gφ (em.inv.app X), Iso.inv_hom_id_app, Functor.map_id,
    Category.id_comp, hcφ]

variable (W : MorphismProperty H) [q.IsLocalization W]

/-- The cocycle condition for three lifted transitions, read at an arbitrary object of the
localization: the transition of a composite, precomposed with the comparison of the composite,
is the composite of the two transitions. -/
theorem liftedTransition_cocycle
    (fac : ∀ Y : Hl, cmp.app (ql.obj Y) ≫ cχ.app Y =
      Gφ.map (cψ.app Y) ≫ cφ.app (Gψh.obj Y) ≫ qn.map (cmph.app Y))
    (cocycle : ∀ X : H, cmph.app (Flh.obj X) ≫ τχ.app X =
      Gφh.map (τψ.app X) ≫ τφ.app X)
    (Z : D) :
    cmp.app (Fl.obj Z) ≫ (liftedTransition el cχ en τχ W).app Z =
      Gφ.map ((liftedTransition el cψ em τψ W).app Z) ≫
        (liftedTransition em cφ en τφ W).app Z := by
  have key : (Functor.whiskerLeft Fl cmp ≫ liftedTransition el cχ en τχ W :
      Fl ⋙ Gψ ⋙ Gφ ⟶ Fn) =
      Functor.whiskerRight (liftedTransition el cψ em τψ W) Gφ ≫
        liftedTransition em cφ en τφ W := by
    refine Localization.natTrans_ext q W fun X => ?_
    dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    rw [liftedTransition_app_q, liftedTransition_app_q, liftedTransition_app_q,
      ← liftedTransitionComparison_app, ← liftedTransitionComparison_app,
      ← liftedTransitionComparison_app]
    exact liftedTransitionComparison_cocycle el em en cψ cφ cχ cmp cmph τψ τφ τχ fac cocycle X
  exact congr_app key Z

end Cocycle

end CategoryTheory

end
