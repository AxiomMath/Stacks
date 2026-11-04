module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import StacksFrontier.Algebra.Homology.ComponentIso
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.HomComplex

/-!
# Functoriality of the internal Hom complex on a ringed site

Let `(C, O)` be a ringed site. The internal Hom complex `SheafHom(K, L)` of two complexes of
`O`-modules, constructed in `AlgebraicGeometry.RingedSite.sheafHomComplex`, is contravariant in
`K` and covariant in `L`. This file builds that bifunctorial action and proves that it carries a
termwise split short exact sequence of complexes to a termwise split short exact sequence, in
either variable; in the first variable the arrows are reversed.

A morphism of internal Hom complexes is pinned down by the formula its sections obey on every
slice site: `IsInducedSheafHomComplexMap g f H H' h` says that `h` acts on a local section of
`H` by precomposing with `g` and postcomposing with `f`. Two morphisms satisfying that formula
for the same `g` and `f` agree, so the action is supplied once as a single coherent datum
`SheafHomComplexConstruction` rather than chosen independently in each variable.

## Main definitions

* `Stacks.Cohomology.InternalHom.IsInducedSheafHomComplexMap`: the local formula identifying a
  morphism of internal Hom complexes as simultaneous pre- and postcomposition.
* `Stacks.Cohomology.InternalHom.SheafHomComplexConstruction`: the coherent bifunctorial action
  on morphisms of internal Hom complexes.
* `Stacks.Cohomology.InternalHom.sheafHomComplexConstruction`: the canonical such action.
* `Stacks.Cohomology.InternalHom.sheafHomComplexMap`: the induced map of internal Hom complexes.

## Main results

* `Stacks.Cohomology.InternalHom.internalHomComplex_termwiseSplit_first`: the contravariant
  variable carries a termwise split short exact sequence to one with the arrows reversed.
* `Stacks.Cohomology.InternalHom.internalHomComplex_termwiseSplit_second`: the covariant
  variable preserves a termwise split short exact sequence.

## Implementation notes

Termwise split exactness is expressed by a splitting of each degree evaluation, together with
the vanishing of the composite; so the conclusions give genuine short complexes.

The sections of an internal Hom complex over an object are, by construction, Mathlib's
`CochainComplex.HomComplex` of the restrictions to the corresponding slice site, and the
identification is compatible with restriction and with the action of local scalars.

The naturality statements of `AlgebraicGeometry.RingedSite.SheafHomComplex` identify a section
of the slice over `U` with a section of the original site, so they are not type-correct at
reducible transparency and cannot be used by `rw`. The abbreviation `applyOver` carries that
identification in its own type, and `applyOver_restrict`, `applyOver_smul`,
`applyOver_precomp_section` and `applyOver_postcomp_section` restate what is needed in terms of
it.

## References

* [Stacks Project, Tag 0A8X](https://stacks.math.columbia.edu/tag/0A8X)
* [Stacks Project, Tag 08JC](https://stacks.math.columbia.edu/tag/08JC)
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.RingedSite Stacks.Homology

universe u v r w

namespace Stacks.Cohomology.InternalHom

/-- Restriction of sheaves of modules to the slice site over `U` preserves zero morphisms. -/
noncomputable local instance (X : RingedSite.{u, v, r})
    [HasWeakSheafify X.J AddCommGrpCat.{max u v w}] (U : X.C) :
    (SheafOfModules.overFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).PreservesZeroMorphisms where
  map_zero {A B} := by
    ext V x
    rfl

/-- A morphism of internal Hom complexes induced contravariantly by `g` and covariantly by `f`. -/
def IsInducedSheafHomComplexMap {X : RingedSite.{u, v, r}}
    [HasWeakSheafify X.J AddCommGrpCat.{max u v w}]
    {K K' L L' : CochainComplex
      (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (g : K' ⟶ K) (f : L ⟶ L')
    (H : SheafHomComplex X K L) (H' : SheafHomComplex X K' L')
    (h : H.obj ⟶ H'.obj) : Prop :=
  ∀ (U : X.C) (n p q : ℤ) (hpq : p + n = q)
    (s : (H.obj.X n).val.obj (op U)),
    (AddCommGrpCat.Hom.hom ((H'.sectionsIso U).hom.f n)
      ((h.f n).val.app (op U) s)).v p q hpq =
      (show (restrictComplex X K' U).X p ⟶ (restrictComplex X K U).X p from
        (g.f p).over U) ≫
        (AddCommGrpCat.Hom.hom ((H.sectionsIso U).hom.f n) s).v p q hpq ≫
          (show (restrictComplex X L U).X q ⟶ (restrictComplex X L' U).X q from
            (f.f q).over U)

/-- The coherent bifunctorial action on morphisms of the internal Hom complexes. -/
structure SheafHomComplexConstruction (X : RingedSite.{u, v, r})
    [HasWeakSheafify X.J AddCommGrpCat.{max u v w}] where
  /-- Simultaneous precomposition and postcomposition. -/
  map : {K K' L L' : CochainComplex
      (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ} →
    (K' ⟶ K) → (L ⟶ L') →
      ((sheafHomComplex X K L).obj ⟶ (sheafHomComplex X K' L').obj)
  /-- The map has the expected description on every slice site. -/
  map_isInduced : ∀ {K K' L L' : CochainComplex
      (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (g : K' ⟶ K) (f : L ⟶ L'),
    IsInducedSheafHomComplexMap g f
      (sheafHomComplex X K L) (sheafHomComplex X K' L') (map g f)
  /-- Identity maps induce the identity. -/
  map_id : ∀ (K L : CochainComplex
      (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    map (𝟙 K) (𝟙 L) = 𝟙 (sheafHomComplex X K L).obj
  /-- Induced maps respect simultaneous composition. -/
  map_comp : ∀ {K₀ K₁ K₂ L₀ L₁ L₂ : CochainComplex
      (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (g₁ : K₁ ⟶ K₀) (g₂ : K₂ ⟶ K₁) (f₁ : L₀ ⟶ L₁) (f₂ : L₁ ⟶ L₂),
    map g₁ f₁ ≫ map g₂ f₂ = map (g₂ ≫ g₁) (f₁ ≫ f₂)

section ApplyOver

variable {X : RingedSite.{u, v, r}}
  {A B K : CochainComplex
      (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}

/-- The value of a degree-`n` local section `s` of an internal Hom complex on a degree-`p`
section of its source over an object `V` of the site mapping to `U` by `g`, with both the
argument and the result spelled in the original site. -/
noncomputable abbrev applyOver (H : SheafHomComplex X A B) (U : X.C) (n p q : ℤ)
    (hpq : p + n = q) (s : (H.obj.X n).val.obj (op U)) {V : X.C} (g : V ⟶ U)
    (x : (A.X p).val.obj (op V)) : (B.X q).val.obj (op V) :=
  (((AddCommGrpCat.Hom.hom ((H.sectionsIso U).hom.f n) s).v p q hpq).val.app
    (op (Over.mk g))) x

/-- `AlgebraicGeometry.RingedSite.SheafHomComplex.restrict_natural`, read through
`applyOver`. -/
lemma applyOver_restrict (H : SheafHomComplex X A B) {U V : X.C} (i : V ⟶ U) (n p q : ℤ)
    (hpq : p + n = q) (s : (H.obj.X n).val.obj (op U)) {W : X.C} (g : W ⟶ V)
    (x : (A.X p).val.obj (op W)) :
    applyOver H U n p q hpq s (g ≫ i) x =
      applyOver H V n p q hpq ((H.obj.X n).val.map i.op s) g x :=
  H.restrict_natural i n p q hpq s g x

/-- `AlgebraicGeometry.RingedSite.SheafHomComplex.smul_natural`, read through `applyOver`. -/
lemma applyOver_smul (H : SheafHomComplex X A B) (U : X.C)
    (c : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)) (n p q : ℤ) (hpq : p + n = q)
    (s : (H.obj.X n).val.obj (op U)) {V : X.C} (g : V ⟶ U)
    (x : (A.X p).val.obj (op V)) :
    applyOver H U n p q hpq (c • s) g x =
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map g.op c) •
        applyOver H U n p q hpq s g x :=
  H.smul_natural U c n p q hpq s g x

end ApplyOver

/-- Precomposition on local Hom cochains. -/
noncomputable abbrev cochainPrecomp {X : RingedSite.{u, v, r}}
    [HasWeakSheafify X.J AddCommGrpCat.{max u v w}]
    {A B K : CochainComplex
      (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (f : ∀ p, A.X p ⟶ B.X p) (U : X.C) (n : ℤ) :
    ((restrictComplex X B U).HomComplex (restrictComplex X K U)).X n ⟶
      ((restrictComplex X A U).HomComplex (restrictComplex X K U)).X n :=
  AddCommGrpCat.ofHom
    { toFun := fun z => CochainComplex.HomComplex.Cochain.mk
        (fun p q hpq => (f p).over U ≫ z.v p q hpq)
      map_zero' := by ext; simp
      map_add' := by
        intro z w
        ext
        simp [Preadditive.comp_add] }

/-- Postcomposition on local Hom cochains. -/
noncomputable abbrev cochainPostcomp {X : RingedSite.{u, v, r}}
    [HasWeakSheafify X.J AddCommGrpCat.{max u v w}]
    {K A B : CochainComplex
      (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (f : ∀ q, A.X q ⟶ B.X q) (U : X.C) (n : ℤ) :
    ((restrictComplex X K U).HomComplex (restrictComplex X A U)).X n ⟶
      ((restrictComplex X K U).HomComplex (restrictComplex X B U)).X n :=
  AddCommGrpCat.ofHom
    { toFun := fun z => CochainComplex.HomComplex.Cochain.mk
        (fun p q hpq => z.v p q hpq ≫ (f q).over U)
      map_zero' := by ext; simp
      map_add' := by
        intro z w
        ext
        simp [Preadditive.add_comp] }

section ApplyOverSection

variable {X : RingedSite.{u, v, r}} [HasWeakSheafify X.J AddCommGrpCat.{max u v w}]
  {A B K : CochainComplex
      (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}

/-- The local description of `precompDegreeMap`: it precomposes with `f p`. -/
lemma applyOver_precomp_section (H : SheafHomComplex X B K) (H' : SheafHomComplex X A K)
    (f : ∀ p, A.X p ⟶ B.X p) (U : X.C) (n p q : ℤ) (hpq : p + n = q)
    (s : (H.obj.X n).val.obj (op U)) {V : X.C} (g : V ⟶ U)
    (x : (A.X p).val.obj (op V)) :
    applyOver H' U n p q hpq
        (((H'.sectionsIso U).inv.f n).hom
          ((cochainPrecomp f U n).hom
            (((H.sectionsIso U).hom.f n).hom s))) g x =
      applyOver H U n p q hpq s g ((f p).val.app (op V) x) :=
  congrArg (fun z : CochainComplex.HomComplex.Cochain
      (restrictComplex X A U) (restrictComplex X K U) n =>
        (show (K.X q).val.obj (op V) from
          ((z.v p q hpq).val.app (op (Over.mk g))) x))
    (componentIso_inv_hom_apply (H'.sectionsIso U) n _)

/-- The local description of `postcompDegreeMap`: it postcomposes with `f q`. -/
lemma applyOver_postcomp_section (H : SheafHomComplex X K A) (H' : SheafHomComplex X K B)
    (f : ∀ q, A.X q ⟶ B.X q) (U : X.C) (n p q : ℤ) (hpq : p + n = q)
    (s : (H.obj.X n).val.obj (op U)) {V : X.C} (g : V ⟶ U)
    (x : (K.X p).val.obj (op V)) :
    applyOver H' U n p q hpq
        (((H'.sectionsIso U).inv.f n).hom
          ((cochainPostcomp f U n).hom
            (((H.sectionsIso U).hom.f n).hom s))) g x =
      (f q).val.app (op V) (applyOver H U n p q hpq s g x) :=
  congrArg (fun z : CochainComplex.HomComplex.Cochain
      (restrictComplex X K U) (restrictComplex X B U) n =>
        (show (B.X q).val.obj (op V) from
          ((z.v p q hpq).val.app (op (Over.mk g))) x))
    (componentIso_inv_hom_apply (H'.sectionsIso U) n _)

end ApplyOverSection

/-- Precomposition by `f` in a single degree of the internal Hom complex. -/
noncomputable def precompDegreeMap {X : RingedSite.{u, v, r}}
    [HasWeakSheafify X.J AddCommGrpCat.{max u v w}]
    {A B K : CochainComplex
      (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (H : SheafHomComplex X B K) (H' : SheafHomComplex X A K)
    (f : ∀ p, A.X p ⟶ B.X p) (n : ℤ) : H.obj.X n ⟶ H'.obj.X n := by
  let app (U : X.Cᵒᵖ) :
      (H.obj.X n).val.obj U ⟶ (H'.obj.X n).val.obj U := ModuleCat.ofHom (by
    refine
      { toFun := fun s ↦ ((H'.sectionsIso U.unop).inv.f n).hom
          ((cochainPrecomp f U.unop n).hom
            (((H.sectionsIso U.unop).hom.f n).hom s))
        map_add' := ?_
        map_smul' := ?_ }
    · intro x y
      exact map_add (((H'.sectionsIso U.unop).inv.f n).hom.comp
        ((cochainPrecomp f U.unop n).hom.comp ((H.sectionsIso U.unop).hom.f n).hom)) x y
    · intro c s
      apply componentIso_hom_injective (H'.sectionsIso U.unop) n
      rw [componentIso_inv_hom_apply (H'.sectionsIso U.unop) n]
      apply CochainComplex.HomComplex.Cochain.ext
      intro p q hpq
      ext W x
      obtain ⟨⟨V, ⟨⟩, g⟩⟩ := W
      refine (applyOver_smul H U.unop c n p q hpq s g
        ((f p).val.app (op V) x)).trans ?_
      refine Eq.trans ?_ (applyOver_smul H' U.unop c n p q hpq
        (((H'.sectionsIso U.unop).inv.f n).hom
          ((cochainPrecomp f U.unop n).hom
            (((H.sectionsIso U.unop).hom.f n).hom s))) g x).symm
      exact congrArg (fun y : (K.X q).val.obj (op V) =>
          ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map g.op c) • y)
        (applyOver_precomp_section H H' f U.unop n p q hpq s g x).symm)
  refine ⟨?_⟩
  refine { app := app, naturality := ?_ }
  intro U V i
  ext s
  apply componentIso_hom_injective (H'.sectionsIso V.unop) n
  change ((H'.sectionsIso V.unop).hom.f n).hom
      (((H'.sectionsIso V.unop).inv.f n).hom
        ((cochainPrecomp f V.unop n).hom
          (((H.sectionsIso V.unop).hom.f n).hom ((H.obj.X n).val.map i s)))) =
    ((H'.sectionsIso V.unop).hom.f n).hom ((H'.obj.X n).val.map i (app U s))
  rw [componentIso_inv_hom_apply (H'.sectionsIso V.unop) n]
  apply CochainComplex.HomComplex.Cochain.ext
  intro p q hpq
  ext W y
  obtain ⟨⟨W', ⟨⟩, g⟩⟩ := W
  refine Eq.trans ?_ (applyOver_restrict H' i.unop n p q hpq (app U s) g y)
  refine Eq.trans (applyOver_restrict H i.unop n p q hpq s g
    ((f p).val.app (op W') y)).symm ?_
  exact (applyOver_precomp_section H H' f U.unop n p q hpq s (g ≫ i.unop) y).symm

/-- Postcomposition by `f` in a single degree of the internal Hom complex. -/
noncomputable def postcompDegreeMap {X : RingedSite.{u, v, r}}
    [HasWeakSheafify X.J AddCommGrpCat.{max u v w}]
    {K A B : CochainComplex
      (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (H : SheafHomComplex X K A) (H' : SheafHomComplex X K B)
    (f : ∀ q, A.X q ⟶ B.X q) (n : ℤ) : H.obj.X n ⟶ H'.obj.X n := by
  let app (U : X.Cᵒᵖ) :
      (H.obj.X n).val.obj U ⟶ (H'.obj.X n).val.obj U := ModuleCat.ofHom (by
    refine
      { toFun := fun s ↦ ((H'.sectionsIso U.unop).inv.f n).hom
          ((cochainPostcomp f U.unop n).hom
            (((H.sectionsIso U.unop).hom.f n).hom s))
        map_add' := ?_
        map_smul' := ?_ }
    · intro x y
      exact map_add (((H'.sectionsIso U.unop).inv.f n).hom.comp
        ((cochainPostcomp f U.unop n).hom.comp ((H.sectionsIso U.unop).hom.f n).hom)) x y
    · intro c s
      apply componentIso_hom_injective (H'.sectionsIso U.unop) n
      rw [componentIso_inv_hom_apply (H'.sectionsIso U.unop) n]
      apply CochainComplex.HomComplex.Cochain.ext
      intro p q hpq
      ext W x
      obtain ⟨⟨V, ⟨⟩, g⟩⟩ := W
      refine Eq.trans ?_ (applyOver_smul H' U.unop c n p q hpq
        (((H'.sectionsIso U.unop).inv.f n).hom
          ((cochainPostcomp f U.unop n).hom
            (((H.sectionsIso U.unop).hom.f n).hom s))) g x).symm
      refine Eq.trans (congrArg (fun y : (A.X q).val.obj (op V) =>
          (f q).val.app (op V) y) (applyOver_smul H U.unop c n p q hpq s g x)) ?_
      refine Eq.trans (map_smul ((f q).val.app (op V)).hom _ _) ?_
      exact congrArg (fun y : (B.X q).val.obj (op V) =>
          ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map g.op c) • y)
        (applyOver_postcomp_section H H' f U.unop n p q hpq s g x).symm)
  refine ⟨?_⟩
  refine { app := app, naturality := ?_ }
  intro U V i
  ext s
  apply componentIso_hom_injective (H'.sectionsIso V.unop) n
  change ((H'.sectionsIso V.unop).hom.f n).hom
      (((H'.sectionsIso V.unop).inv.f n).hom
        ((cochainPostcomp f V.unop n).hom
          (((H.sectionsIso V.unop).hom.f n).hom ((H.obj.X n).val.map i s)))) =
    ((H'.sectionsIso V.unop).hom.f n).hom ((H'.obj.X n).val.map i (app U s))
  rw [componentIso_inv_hom_apply (H'.sectionsIso V.unop) n]
  apply CochainComplex.HomComplex.Cochain.ext
  intro p q hpq
  ext W y
  obtain ⟨⟨W', ⟨⟩, g⟩⟩ := W
  refine Eq.trans ?_ (applyOver_restrict H' i.unop n p q hpq (app U s) g y)
  refine Eq.trans (congrArg (fun z : (A.X q).val.obj (op W') => (f q).val.app (op W') z)
    (applyOver_restrict H i.unop n p q hpq s g y).symm) ?_
  exact (applyOver_postcomp_section H H' f U.unop n p q hpq s (g ≫ i.unop) y).symm

section Section

variable {X : RingedSite.{u, v, r}} [HasWeakSheafify X.J AddCommGrpCat.{max u v w}]

omit [HasWeakSheafify X.J AddCommGrpCat.{max u v w}] in
private lemma sectionsIso_d_apply
    {A B : CochainComplex
      (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (H : SheafHomComplex X A B) (U : X.C) (n m : ℤ)
    (s : (H.obj.X n).val.obj (op U)) :
    ((H.sectionsIso U).hom.f m).hom
        ((H.obj.d n m).val.app (op U) s) =
      CochainComplex.HomComplex.δ n m
        (((H.sectionsIso U).hom.f n).hom s) :=
  (congrArg (fun f => f s) ((H.sectionsIso U).hom.comm n m)).symm

/-- The local Hom cochain attached to a section of the internal Hom complex. -/
private noncomputable abbrev sectionCochain
    {A B : CochainComplex
      (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (H : SheafHomComplex X A B) (U : X.C) (n : ℤ)
    (s : (H.obj.X n).val.obj (op U)) :
    CochainComplex.HomComplex.Cochain (restrictComplex X A U) (restrictComplex X B U) n :=
  ((H.sectionsIso U).hom.f n).hom s

omit [HasWeakSheafify X.J AddCommGrpCat.{max u v w}] in
private lemma sectionCochain_d
    {A B : CochainComplex
      (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (H : SheafHomComplex X A B) (U : X.C) (n m : ℤ)
    (s : (H.obj.X n).val.obj (op U)) :
    sectionCochain H U m ((H.obj.d n m).val.app (op U) s) =
      CochainComplex.HomComplex.δ n m (sectionCochain H U n s) :=
  sectionsIso_d_apply H U n m s

private lemma sectionCochain_precomp
    {A B K : CochainComplex
      (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (H : SheafHomComplex X B K) (H' : SheafHomComplex X A K)
    (f : ∀ p, A.X p ⟶ B.X p) (U : X.C) (n p q : ℤ) (hpq : p + n = q)
    (s : (H.obj.X n).val.obj (op U)) :
    (sectionCochain H' U n ((precompDegreeMap H H' f n).val.app (op U) s)).v p q hpq =
      (f p).over U ≫ (sectionCochain H U n s).v p q hpq := by
  show (((H'.sectionsIso U).hom.f n).hom
    (((H'.sectionsIso U).inv.f n).hom _)).v p q hpq = _
  rw [componentIso_inv_hom_apply (H'.sectionsIso U) n]
  rfl

private lemma sectionCochain_postcomp
    {K A B : CochainComplex
      (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (H : SheafHomComplex X K A) (H' : SheafHomComplex X K B)
    (f : ∀ q, A.X q ⟶ B.X q) (U : X.C) (n p q : ℤ) (hpq : p + n = q)
    (s : (H.obj.X n).val.obj (op U)) :
    (sectionCochain H' U n ((postcompDegreeMap H H' f n).val.app (op U) s)).v p q hpq =
      (sectionCochain H U n s).v p q hpq ≫ (f q).over U := by
  show (((H'.sectionsIso U).hom.f n).hom
    (((H'.sectionsIso U).inv.f n).hom _)).v p q hpq = _
  rw [componentIso_inv_hom_apply (H'.sectionsIso U) n]
  rfl

/-- Degreewise restriction of a morphism of complexes to a slice site. -/
noncomputable abbrev restrictMap
    {A B : CochainComplex
      (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (g : A ⟶ B) (U : X.C) : restrictComplex X A U ⟶ restrictComplex X B U :=
  ((SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapHomologicalComplex
    (ComplexShape.up ℤ)).map g

private lemma restrictMap_f
    {A B : CochainComplex
      (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (g : A ⟶ B) (U : X.C) (p : ℤ) :
    (restrictMap g U).f p = (g.f p).over U := rfl

private lemma sectionCochain_precomp_comp
    {A B K : CochainComplex
      (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (H : SheafHomComplex X B K) (H' : SheafHomComplex X A K)
    (g : A ⟶ B) (U : X.C) (n : ℤ) (s : (H.obj.X n).val.obj (op U)) :
    sectionCochain H' U n ((precompDegreeMap H H' (fun p => g.f p) n).val.app (op U) s) =
      (CochainComplex.HomComplex.Cochain.ofHom (restrictMap g U)).comp
        (sectionCochain H U n s) (zero_add n) := by
  apply CochainComplex.HomComplex.Cochain.ext
  intro p q hpq
  simpa only [CochainComplex.HomComplex.Cochain.zero_cochain_comp_v,
      CochainComplex.HomComplex.Cochain.ofHom_v, restrictMap_f] using
    sectionCochain_precomp H H' (fun p => g.f p) U n p q hpq s

private lemma sectionCochain_postcomp_comp
    {K A B : CochainComplex
      (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (H : SheafHomComplex X K A) (H' : SheafHomComplex X K B)
    (g : A ⟶ B) (U : X.C) (n : ℤ) (s : (H.obj.X n).val.obj (op U)) :
    sectionCochain H' U n ((postcompDegreeMap H H' (fun q => g.f q) n).val.app (op U) s) =
      (sectionCochain H U n s).comp (CochainComplex.HomComplex.Cochain.ofHom
        (restrictMap g U)) (add_zero n) := by
  apply CochainComplex.HomComplex.Cochain.ext
  intro p q hpq
  simpa only [CochainComplex.HomComplex.Cochain.comp_zero_cochain_v,
      CochainComplex.HomComplex.Cochain.ofHom_v, restrictMap_f] using
    sectionCochain_postcomp H H' (fun q => g.f q) U n p q hpq s

omit [HasWeakSheafify X.J AddCommGrpCat.{max u v w}] in
private lemma over_id (A : SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (U : X.C) :
    SheafOfModules.Hom.over (𝟙 A) U = 𝟙 (A.over U) := by
  ext V x
  rfl

omit [HasWeakSheafify X.J AddCommGrpCat.{max u v w}] in
private lemma over_comp
    {A B C : SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (f : A ⟶ B)
    (g : B ⟶ C)
    (U : X.C) : (f ≫ g).over U = f.over U ≫ g.over U := by
  ext V x
  rfl

omit [HasWeakSheafify X.J AddCommGrpCat.{max u v w}] in
private lemma over_add
    {A B : SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (f g : A ⟶ B) (U : X.C) : (f + g).over U = f.over U + g.over U := by
  ext V x
  rfl

omit [HasWeakSheafify X.J AddCommGrpCat.{max u v w}] in
private lemma over_zero
    {A B : SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (U : X.C) :
    (0 : A ⟶ B).over U = 0 := by
  ext V x
  rfl

/-- Two morphisms of internal Hom complexes induced by the same pair of maps are equal. -/
lemma induced_map_ext
    {K K' L L' : CochainComplex
      (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    {H : SheafHomComplex X K L} {H' : SheafHomComplex X K' L'}
    {g : K' ⟶ K} {f : L ⟶ L'} {h₁ h₂ : H.obj ⟶ H'.obj}
    (hh₁ : IsInducedSheafHomComplexMap g f H H' h₁)
    (hh₂ : IsInducedSheafHomComplexMap g f H H' h₂) : h₁ = h₂ := by
  refine HomologicalComplex.Hom.ext (funext fun n => ?_)
  ext U s
  exact componentIso_hom_injective (H'.sectionsIso U.unop) n <|
    CochainComplex.HomComplex.Cochain.ext _ _ fun p q hpq =>
      (hh₁ U.unop n p q hpq s).trans (hh₂ U.unop n p q hpq s).symm

/-- A composite of induced maps is induced by the composite maps. -/
lemma induced_map_comp
    {K₀ K₁ K₂ L₀ L₁ L₂ : CochainComplex
      (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    {H₀ : SheafHomComplex X K₀ L₀} {H₁ : SheafHomComplex X K₁ L₁}
    {H₂ : SheafHomComplex X K₂ L₂}
    {g₁ : K₁ ⟶ K₀} {g₂ : K₂ ⟶ K₁} {f₁ : L₀ ⟶ L₁} {f₂ : L₁ ⟶ L₂}
    {h₁ : H₀.obj ⟶ H₁.obj} {h₂ : H₁.obj ⟶ H₂.obj}
    (hh₁ : IsInducedSheafHomComplexMap g₁ f₁ H₀ H₁ h₁)
    (hh₂ : IsInducedSheafHomComplexMap g₂ f₂ H₁ H₂ h₂) :
    IsInducedSheafHomComplexMap (g₂ ≫ g₁) (f₁ ≫ f₂) H₀ H₂ (h₁ ≫ h₂) := by
  intro U n p q hpq s
  have hsecond := hh₂ U n p q hpq ((h₁.f n).val.app (op U) s)
  rw [hh₁ U n p q hpq s] at hsecond
  calc
    _ = (g₂.f p).over U ≫
          ((g₁.f p).over U ≫
            (AddCommGrpCat.Hom.hom ((H₀.sectionsIso U).hom.f n) s).v p q hpq) ≫
          (f₁.f q).over U ≫ (f₂.f q).over U := by
            simpa [Category.assoc] using hsecond
    _ = (g₂.f p ≫ g₁.f p).over U ≫
          (AddCommGrpCat.Hom.hom ((H₀.sectionsIso U).hom.f n) s).v p q hpq ≫
          (f₁.f q ≫ f₂.f q).over U := by
            rw [over_comp, over_comp]
            simp only [Category.assoc]

/-- Precomposition by `g` on the internal Hom complex. -/
noncomputable def precompComplexMap
    {A B K : CochainComplex
      (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (H : SheafHomComplex X B K) (H' : SheafHomComplex X A K) (g : A ⟶ B) :
    H.obj ⟶ H'.obj where
  f n := precompDegreeMap H H' (fun p => g.f p) n
  comm' n m _ := by
    ext U s
    apply componentIso_hom_injective (H'.sectionsIso U.unop) m
    change ((H'.sectionsIso U.unop).hom.f m).hom
        ((H'.obj.d n m).val.app (op U.unop)
          ((precompDegreeMap H H' (fun p => g.f p) n).val.app (op U.unop) s)) =
      ((H'.sectionsIso U.unop).hom.f m).hom
        ((precompDegreeMap H H' (fun p => g.f p) m).val.app (op U.unop)
          ((H.obj.d n m).val.app (op U.unop) s))
    rw [sectionsIso_d_apply H' U.unop n m]
    change CochainComplex.HomComplex.δ n m
        (sectionCochain H' U.unop n
          ((precompDegreeMap H H' (fun p => g.f p) n).val.app (op U.unop) s)) =
      sectionCochain H' U.unop m
        ((precompDegreeMap H H' (fun p => g.f p) m).val.app (op U.unop)
          ((H.obj.d n m).val.app (op U.unop) s))
    rw [sectionCochain_precomp_comp H H' g U.unop n s]
    rw [sectionCochain_precomp_comp H H' g U.unop m
      ((H.obj.d n m).val.app (op U.unop) s)]
    rw [sectionCochain_d H U.unop n m s]
    exact CochainComplex.HomComplex.δ_ofHom_comp _ _ _

/-- Postcomposition by `g` on the internal Hom complex. -/
noncomputable def postcompComplexMap
    {K A B : CochainComplex
      (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (H : SheafHomComplex X K A) (H' : SheafHomComplex X K B) (g : A ⟶ B) :
    H.obj ⟶ H'.obj where
  f n := postcompDegreeMap H H' (fun q => g.f q) n
  comm' n m _ := by
    ext U s
    apply componentIso_hom_injective (H'.sectionsIso U.unop) m
    change ((H'.sectionsIso U.unop).hom.f m).hom
        ((H'.obj.d n m).val.app (op U.unop)
          ((postcompDegreeMap H H' (fun q => g.f q) n).val.app (op U.unop) s)) =
      ((H'.sectionsIso U.unop).hom.f m).hom
        ((postcompDegreeMap H H' (fun q => g.f q) m).val.app (op U.unop)
          ((H.obj.d n m).val.app (op U.unop) s))
    rw [sectionsIso_d_apply H' U.unop n m]
    change CochainComplex.HomComplex.δ n m
        (sectionCochain H' U.unop n
          ((postcompDegreeMap H H' (fun q => g.f q) n).val.app (op U.unop) s)) =
      sectionCochain H' U.unop m
        ((postcompDegreeMap H H' (fun q => g.f q) m).val.app (op U.unop)
          ((H.obj.d n m).val.app (op U.unop) s))
    rw [sectionCochain_postcomp_comp H H' g U.unop n s]
    rw [sectionCochain_postcomp_comp H H' g U.unop m
      ((H.obj.d n m).val.app (op U.unop) s)]
    rw [sectionCochain_d H U.unop n m s]
    have hδ : ∀ (z : CochainComplex.HomComplex.Cochain
        (restrictComplex X K U.unop) (restrictComplex X A U.unop) n),
        CochainComplex.HomComplex.δ n m
          (z.comp (CochainComplex.HomComplex.Cochain.ofHom (restrictMap g U.unop))
            (add_zero n)) =
        (CochainComplex.HomComplex.δ n m z).comp
          (CochainComplex.HomComplex.Cochain.ofHom (restrictMap g U.unop)) (add_zero m) :=
      fun z => CochainComplex.HomComplex.δ_comp_ofHom _ _ _
    apply CochainComplex.HomComplex.Cochain.ext
    intro p q hpq
    ext W x
    simpa [cochainPostcomp, sectionCochain] using
      congrArg (fun z => (z.v p q hpq).val.app W x) (hδ (sectionCochain H U.unop n s))

/-- The composite of precomposition by `g` and postcomposition by `f` on internal Hom
complexes. -/
noncomputable def canonicalSheafHomComplexMap (X : RingedSite.{u, v, r})
    [HasWeakSheafify X.J AddCommGrpCat.{max u v w}]
    {K K' L L' : CochainComplex
      (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (g : K' ⟶ K) (f : L ⟶ L') :
    (sheafHomComplex X K L).obj ⟶ (sheafHomComplex X K' L').obj :=
  precompComplexMap (sheafHomComplex X K L) (sheafHomComplex X K' L) g ≫
    postcompComplexMap (sheafHomComplex X K' L) (sheafHomComplex X K' L') f

/-- `canonicalSheafHomComplexMap X g f` is induced contravariantly by `g` and covariantly
by `f`. -/
lemma canonicalSheafHomComplexMap_induced (X : RingedSite.{u, v, r})
    [HasWeakSheafify X.J AddCommGrpCat.{max u v w}]
    {K K' L L' : CochainComplex
      (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (g : K' ⟶ K) (f : L ⟶ L') :
    IsInducedSheafHomComplexMap g f (sheafHomComplex X K L)
      (sheafHomComplex X K' L') (canonicalSheafHomComplexMap X g f) := by
  intro U n p q hpq s
  show ((sectionCochain (sheafHomComplex X K' L') U n
      ((postcompDegreeMap (sheafHomComplex X K' L) (sheafHomComplex X K' L')
          (fun q => f.f q) n).val.app (op U)
        ((precompDegreeMap (sheafHomComplex X K L) (sheafHomComplex X K' L)
          (fun p => g.f p) n).val.app (op U) s))).v p q hpq) = _
  rw [sectionCochain_postcomp (sheafHomComplex X K' L) (sheafHomComplex X K' L')
    (fun q => f.f q) U n p q hpq
    ((precompDegreeMap (sheafHomComplex X K L) (sheafHomComplex X K' L)
      (fun p => g.f p) n).val.app (op U) s)]
  rw [sectionCochain_precomp (sheafHomComplex X K L) (sheafHomComplex X K' L)
    (fun p => g.f p) U n p q hpq s]
  rfl

/-- The identity of an internal Hom complex is induced by the identities. -/
lemma identitySheafHomComplexMap_induced (X : RingedSite.{u, v, r})
    [HasWeakSheafify X.J AddCommGrpCat.{max u v w}]
    {K L : CochainComplex
      (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (H : SheafHomComplex X K L) :
    IsInducedSheafHomComplexMap (𝟙 K) (𝟙 L) H H (𝟙 H.obj) := by
  intro U n p q hpq s
  show (sectionCochain H U n s).v p q hpq = _
  simp [HomologicalComplex.id_f]

/-- The canonical precomposition-and-postcomposition action on the internal Hom complexes,
with its local formula and its bifunctoriality. -/
noncomputable def sheafHomComplexConstruction (X : RingedSite.{u, v, r})
    [HasWeakSheafify X.J AddCommGrpCat.{max u v w}] :
    SheafHomComplexConstruction X where
  map {_ _ _ _} g f := canonicalSheafHomComplexMap X g f
  map_isInduced g f := canonicalSheafHomComplexMap_induced X g f
  map_id K L :=
    induced_map_ext (canonicalSheafHomComplexMap_induced X (𝟙 K) (𝟙 L))
      (identitySheafHomComplexMap_induced X (sheafHomComplex X K L))
  map_comp g₁ g₂ f₁ f₂ :=
    induced_map_ext
      (induced_map_comp
        (canonicalSheafHomComplexMap_induced X g₁ f₁)
        (canonicalSheafHomComplexMap_induced X g₂ f₂))
      (canonicalSheafHomComplexMap_induced X (g₂ ≫ g₁) (f₁ ≫ f₂))

/-- The map of internal Hom complexes induced by precomposition with `g` and postcomposition
with `f`. -/
noncomputable abbrev sheafHomComplexMap (X : RingedSite.{u, v, r})
    [HasWeakSheafify X.J AddCommGrpCat.{max u v w}]
    {K K' L L' : CochainComplex
      (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (g : K' ⟶ K) (f : L ⟶ L') :
    (sheafHomComplex X K L).obj ⟶ (sheafHomComplex X K' L').obj :=
  (sheafHomComplexConstruction X).map g f

omit [HasWeakSheafify X.J AddCommGrpCat.{max u v w}] in
private lemma sectionCochain_zero
    {A B : CochainComplex
      (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (H : SheafHomComplex X A B) (U : X.C) (n : ℤ) :
    sectionCochain H U n 0 = 0 := map_zero _

omit [HasWeakSheafify X.J AddCommGrpCat.{max u v w}] in
private lemma sectionCochain_add
    {A B : CochainComplex
      (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (H : SheafHomComplex X A B) (U : X.C) (n : ℤ)
    (s t : (H.obj.X n).val.obj (op U)) :
    sectionCochain H U n (s + t) =
      sectionCochain H U n s + sectionCochain H U n t := map_add _ _ _

omit [HasWeakSheafify X.J AddCommGrpCat.{max u v w}] in
private lemma degreeMap_ext
    {A B : CochainComplex
      (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (H : SheafHomComplex X A B)
    {P : SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} {n : ℤ}
    {f g : P ⟶ H.obj.X n}
    (h : ∀ (U : X.C) (s : P.val.obj (op U)) (p q : ℤ) (hpq : p + n = q),
      (sectionCochain H U n ((f.val.app (op U)) s)).v p q hpq =
        (sectionCochain H U n ((g.val.app (op U)) s)).v p q hpq) : f = g := by
  ext U s
  exact componentIso_hom_injective (H.sectionsIso U.unop) n
    (CochainComplex.HomComplex.Cochain.ext _ _ (h U.unop s))

/-- The restriction of the identity morphism of a complex to a slice site is the identity. -/
private lemma over_id_f {Y : RingedSite.{u, v, r}}
    (K : CochainComplex
      (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (p : ℤ) (U : Y.C) :
    SheafOfModules.Hom.over (HomologicalComplex.Hom.f (𝟙 K) p) U = 𝟙 ((K.X p).over U) := by
  rw [HomologicalComplex.id_f]
  exact over_id _ _

private lemma sectionCochain_induced_precomp
    {A B K : CochainComplex
      (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (H : SheafHomComplex X B K) (H' : SheafHomComplex X A K)
    (f : A ⟶ B) (h : H.obj ⟶ H'.obj)
    (hh : IsInducedSheafHomComplexMap f (𝟙 K) H H' h)
    (U : X.C) (n p q : ℤ) (hpq : p + n = q)
    (s : (H.obj.X n).val.obj (op U)) :
    (sectionCochain H' U n ((h.f n).val.app (op U) s)).v p q hpq =
      (f.f p).over U ≫ (sectionCochain H U n s).v p q hpq := by
  have e := hh U n p q hpq s
  have h₁ := over_id_f K q U
  refine e.trans (congrArg (fun z => (f.f p).over U ≫ z) ?_)
  exact (congrArg (fun z => (sectionCochain H U n s).v p q hpq ≫ z) h₁).trans
    (Category.comp_id _)

private lemma sectionCochain_induced_postcomp
    {K A B : CochainComplex
      (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (H : SheafHomComplex X K A) (H' : SheafHomComplex X K B)
    (f : A ⟶ B) (h : H.obj ⟶ H'.obj)
    (hh : IsInducedSheafHomComplexMap (𝟙 K) f H H' h)
    (U : X.C) (n p q : ℤ) (hpq : p + n = q)
    (s : (H.obj.X n).val.obj (op U)) :
    (sectionCochain H' U n ((h.f n).val.app (op U) s)).v p q hpq =
      (sectionCochain H U n s).v p q hpq ≫ (f.f q).over U := by
  have e := hh U n p q hpq s
  have h₁ := over_id_f K p U
  refine e.trans ?_
  exact (congrArg (fun z => z ≫ (sectionCochain H U n s).v p q hpq ≫ (f.f q).over U) h₁).trans
    (Category.id_comp _)

/-- In the contravariant variable, internal Hom carries a termwise split short exact sequence to
one with the arrows reversed, for an arbitrary choice of internal Hom complexes and an arbitrary
pair of maps satisfying the local formula. -/
private lemma termwiseSplit_first_aux
    (S : ShortComplex
      (CochainComplex (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ))
    (hS : ∀ n, Nonempty ((S.map (HomologicalComplex.eval
      (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ) n)).Splitting))
    (K : CochainComplex (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (H₁ : SheafHomComplex X S.X₁ K) (H₂ : SheafHomComplex X S.X₂ K)
    (H₃ : SheafHomComplex X S.X₃ K)
    (a : H₃.obj ⟶ H₂.obj) (b : H₂.obj ⟶ H₁.obj)
    (ha : IsInducedSheafHomComplexMap S.g (𝟙 K) H₃ H₂ a)
    (hb : IsInducedSheafHomComplexMap S.f (𝟙 K) H₂ H₁ b) :
    ∃ w : a ≫ b = 0, ∀ n, Nonempty
      (((ShortComplex.mk a b w).map (HomologicalComplex.eval
        (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          (ComplexShape.up ℤ) n)).Splitting) := by
  classical
  let t n := (hS n).some
  let rr (n : ℤ) : S.X₂.X n ⟶ S.X₁.X n := (t n).r
  let ss (n : ℤ) : S.X₃.X n ⟶ S.X₂.X n := (t n).s
  have hfr n : S.f.f n ≫ rr n = 𝟙 (S.X₁.X n) := (t n).f_r
  have hsg n : ss n ≫ S.g.f n = 𝟙 (S.X₃.X n) := (t n).s_g
  have hid n : rr n ≫ S.f.f n + S.g.f n ≫ ss n = 𝟙 (S.X₂.X n) := (t n).id
  have hz n : S.f.f n ≫ S.g.f n = 0 := congrArg (fun f => f.f n) S.zero
  have w : a ≫ b = 0 := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply degreeMap_ext H₁
    intro U z p q hpq
    show (sectionCochain H₁ U n
      ((b.f n).val.app (op U) ((a.f n).val.app (op U) z))).v p q hpq =
        (sectionCochain H₁ U n 0).v p q hpq
    rw [sectionCochain_induced_precomp H₂ H₁ S.f b hb,
      sectionCochain_induced_precomp H₃ H₂ S.g a ha, sectionCochain_zero,
      ← Category.assoc, ← over_comp, hz, over_zero, Limits.zero_comp]
    rfl
  refine ⟨w, fun n => ⟨{
    r := precompDegreeMap H₂ H₃ ss n
    s := precompDegreeMap H₁ H₂ rr n
    f_r := ?_
    s_g := ?_
    id := ?_ }⟩⟩
  · apply degreeMap_ext H₃
    intro U z p q hpq
    show (sectionCochain H₃ U n
      ((precompDegreeMap H₂ H₃ ss n).val.app (op U)
        ((a.f n).val.app (op U) z))).v p q hpq =
      (sectionCochain H₃ U n z).v p q hpq
    rw [sectionCochain_precomp, sectionCochain_induced_precomp H₃ H₂ S.g a ha,
      ← Category.assoc, ← over_comp, hsg, over_id, Category.id_comp]
  · apply degreeMap_ext H₁
    intro U z p q hpq
    show (sectionCochain H₁ U n
      ((b.f n).val.app (op U)
        ((precompDegreeMap H₁ H₂ rr n).val.app (op U) z))).v p q hpq =
      (sectionCochain H₁ U n z).v p q hpq
    rw [sectionCochain_induced_precomp H₂ H₁ S.f b hb, sectionCochain_precomp,
      ← Category.assoc, ← over_comp, hfr, over_id, Category.id_comp]
  · apply degreeMap_ext H₂
    intro U z p q hpq
    show (sectionCochain H₂ U n
      ((a.f n).val.app (op U)
        ((precompDegreeMap H₂ H₃ ss n).val.app (op U) z) +
       (precompDegreeMap H₁ H₂ rr n).val.app (op U)
        ((b.f n).val.app (op U) z))).v p q hpq =
      (sectionCochain H₂ U n z).v p q hpq
    rw [sectionCochain_add, CochainComplex.HomComplex.Cochain.add_v,
      sectionCochain_induced_precomp H₃ H₂ S.g a ha,
      sectionCochain_precomp, sectionCochain_precomp,
      sectionCochain_induced_precomp H₂ H₁ S.f b hb,
      ← Category.assoc, ← Category.assoc, ← Preadditive.add_comp,
      ← over_comp, ← over_comp, ← over_add, add_comm, hid, over_id, Category.id_comp]

/-- In the covariant variable, internal Hom preserves a termwise split short exact sequence, for
an arbitrary choice of internal Hom complexes and an arbitrary pair of maps satisfying the local
formula. -/
private lemma termwiseSplit_second_aux
    (S : ShortComplex
      (CochainComplex (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ))
    (hS : ∀ n, Nonempty ((S.map (HomologicalComplex.eval
      (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ) n)).Splitting))
    (K : CochainComplex (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (H₁ : SheafHomComplex X K S.X₁) (H₂ : SheafHomComplex X K S.X₂)
    (H₃ : SheafHomComplex X K S.X₃)
    (a : H₁.obj ⟶ H₂.obj) (b : H₂.obj ⟶ H₃.obj)
    (ha : IsInducedSheafHomComplexMap (𝟙 K) S.f H₁ H₂ a)
    (hb : IsInducedSheafHomComplexMap (𝟙 K) S.g H₂ H₃ b) :
    ∃ w : a ≫ b = 0, ∀ n, Nonempty
      (((ShortComplex.mk a b w).map (HomologicalComplex.eval
        (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          (ComplexShape.up ℤ) n)).Splitting) := by
  classical
  let t n := (hS n).some
  let rr (n : ℤ) : S.X₂.X n ⟶ S.X₁.X n := (t n).r
  let ss (n : ℤ) : S.X₃.X n ⟶ S.X₂.X n := (t n).s
  have hfr n : S.f.f n ≫ rr n = 𝟙 (S.X₁.X n) := (t n).f_r
  have hsg n : ss n ≫ S.g.f n = 𝟙 (S.X₃.X n) := (t n).s_g
  have hid n : rr n ≫ S.f.f n + S.g.f n ≫ ss n = 𝟙 (S.X₂.X n) := (t n).id
  have hz n : S.f.f n ≫ S.g.f n = 0 := congrArg (fun f => f.f n) S.zero
  have w : a ≫ b = 0 := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply degreeMap_ext H₃
    intro U z p q hpq
    show (sectionCochain H₃ U n
      ((b.f n).val.app (op U) ((a.f n).val.app (op U) z))).v p q hpq =
        (sectionCochain H₃ U n 0).v p q hpq
    rw [sectionCochain_induced_postcomp H₂ H₃ S.g b hb,
      sectionCochain_induced_postcomp H₁ H₂ S.f a ha, sectionCochain_zero,
      Category.assoc, ← over_comp, hz, over_zero, Limits.comp_zero]
    rfl
  refine ⟨w, fun n => ⟨{
    r := postcompDegreeMap H₂ H₁ rr n
    s := postcompDegreeMap H₃ H₂ ss n
    f_r := ?_
    s_g := ?_
    id := ?_ }⟩⟩
  · apply degreeMap_ext H₁
    intro U z p q hpq
    show (sectionCochain H₁ U n
      ((postcompDegreeMap H₂ H₁ rr n).val.app (op U)
        ((a.f n).val.app (op U) z))).v p q hpq =
      (sectionCochain H₁ U n z).v p q hpq
    rw [sectionCochain_postcomp, sectionCochain_induced_postcomp H₁ H₂ S.f a ha,
      Category.assoc, ← over_comp, hfr, over_id]
    exact Category.comp_id _
  · apply degreeMap_ext H₃
    intro U z p q hpq
    show (sectionCochain H₃ U n
      ((b.f n).val.app (op U)
        ((postcompDegreeMap H₃ H₂ ss n).val.app (op U) z))).v p q hpq =
      (sectionCochain H₃ U n z).v p q hpq
    rw [sectionCochain_induced_postcomp H₂ H₃ S.g b hb, sectionCochain_postcomp,
      Category.assoc, ← over_comp, hsg, over_id]
    exact Category.comp_id _
  · apply degreeMap_ext H₂
    intro U z p q hpq
    show (sectionCochain H₂ U n
      ((a.f n).val.app (op U)
        ((postcompDegreeMap H₂ H₁ rr n).val.app (op U) z) +
       (postcompDegreeMap H₃ H₂ ss n).val.app (op U)
        ((b.f n).val.app (op U) z))).v p q hpq =
      (sectionCochain H₂ U n z).v p q hpq
    rw [sectionCochain_add, CochainComplex.HomComplex.Cochain.add_v,
      sectionCochain_induced_postcomp H₁ H₂ S.f a ha,
      sectionCochain_postcomp, sectionCochain_postcomp,
      sectionCochain_induced_postcomp H₂ H₃ S.g b hb,
      Category.assoc, Category.assoc, ← Preadditive.comp_add,
      ← over_comp, ← over_comp, ← over_add, hid, over_id]
    exact Category.comp_id _

end Section

/-- Internal Hom reverses a termwise split short exact sequence in its first variable. -/
theorem internalHomComplex_termwiseSplit_first (X : RingedSite.{u, v, r})
    [HasWeakSheafify X.J AddCommGrpCat.{max u v w}]
    (S : ShortComplex
      (CochainComplex (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ))
    (hS : ∀ n, Nonempty
      ((S.map (HomologicalComplex.eval
        (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          (ComplexShape.up ℤ) n)).Splitting))
    (K : CochainComplex
      (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    ∃ w : sheafHomComplexMap X S.g (𝟙 K) ≫
        sheafHomComplexMap X S.f (𝟙 K) = 0,
      ∀ n, Nonempty
      (((ShortComplex.mk (sheafHomComplexMap X S.g (𝟙 K))
          (sheafHomComplexMap X S.f (𝟙 K)) w).map
          (HomologicalComplex.eval
            (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
              (ComplexShape.up ℤ) n)).Splitting) :=
  termwiseSplit_first_aux S hS K
    (sheafHomComplex X S.X₁ K) (sheafHomComplex X S.X₂ K)
    (sheafHomComplex X S.X₃ K)
    (sheafHomComplexMap X S.g (𝟙 K)) (sheafHomComplexMap X S.f (𝟙 K))
    ((sheafHomComplexConstruction X).map_isInduced S.g (𝟙 K))
    ((sheafHomComplexConstruction X).map_isInduced S.f (𝟙 K))

/-- Internal Hom preserves a termwise split short exact sequence in its second variable. -/
theorem internalHomComplex_termwiseSplit_second (X : RingedSite.{u, v, r})
    [HasWeakSheafify X.J AddCommGrpCat.{max u v w}]
    (S : ShortComplex
      (CochainComplex (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ))
    (hS : ∀ n, Nonempty
      ((S.map (HomologicalComplex.eval
        (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          (ComplexShape.up ℤ) n)).Splitting))
    (K : CochainComplex
      (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    ∃ w : sheafHomComplexMap X (𝟙 K) S.f ≫
        sheafHomComplexMap X (𝟙 K) S.g = 0,
      ∀ n, Nonempty
      (((ShortComplex.mk (sheafHomComplexMap X (𝟙 K) S.f)
          (sheafHomComplexMap X (𝟙 K) S.g) w).map
          (HomologicalComplex.eval
            (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
              (ComplexShape.up ℤ) n)).Splitting) :=
  termwiseSplit_second_aux S hS K
    (sheafHomComplex X K S.X₁) (sheafHomComplex X K S.X₂)
    (sheafHomComplex X K S.X₃)
    (sheafHomComplexMap X (𝟙 K) S.f) (sheafHomComplexMap X (𝟙 K) S.g)
    ((sheafHomComplexConstruction X).map_isInduced (𝟙 K) S.f)
    ((sheafHomComplexConstruction X).map_isInduced (𝟙 K) S.g)

end Stacks.Cohomology.InternalHom

end
