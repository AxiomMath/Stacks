module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InternalHomSiteEquivalence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomRestriction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedSectionsOnDerivedObjects

/-!
# Internal Hom of complexes is invariant under an equivalence of ringed sites

Let `(C, O_C)` and `(D, O_D)` be ringed sites and let `e : C ≌ D` be an equivalence of the
underlying sites, continuous in both directions, together with structure maps
`φ : O_C ⟶ e_* O_D` and `ψ : O_D ⟶ (e^{-1})_* O_C` exhibiting the two pushforwards of sheaves
of modules as mutually inverse equivalences — exactly the data of Mathlib's
`SheafOfModules.pushforwardPushforwardEquivalence`. On sheaves of modules the transport of the
internal Hom sheaf of Stacks 03EM along such an equivalence is
`Stacks.SheafOfModules.InternalHom.siteEquivInternalHomIso`. This file raises that statement two
levels, to complexes and then to derived categories:

```
φ_* SheafHom^•(A, B) ≅ SheafHom^•(φ_* A, φ_* B),
φ_* RSheafHom(K, L) ≅ RSheafHom(φ_* K, φ_* L).
```

Both are proved in the pattern of `AlgebraicGeometry.RingedSite.derivedHomRestriction`
([Stacks, Tag 08JB]), with an arbitrary equivalence of ringed sites in place of restriction to
a slice site. Neither statement is a Stacks tag — the tags are stated for restriction along a
localization, which is not an equivalence — so nothing here carries a `@[stacks]` attribute.

## Main definitions

* `AlgebraicGeometry.RingedSite.homComplexMapIso`: a fully faithful additive functor preserves
  the Hom complex of two cochain complexes.
* `AlgebraicGeometry.RingedSite.siteEquivSectionIso`: the identification of the complexes of
  sections, over an object `W` of `C`, of the two sides of the chain-level statement.
* `AlgebraicGeometry.RingedSite.siteEquivSectionLinearEquiv`: that identification in a fixed
  degree, as an `O_C(W)`-linear equivalence.
* `AlgebraicGeometry.RingedSite.siteEquivSheafHomComplexIso`: **the chain-level transport.**
* `AlgebraicGeometry.RingedSite.siteEquivDerivedSheafHomIso`: **the derived-level transport.**

## Main results

* `AlgebraicGeometry.RingedSite.siteEquivSectionIso_apply` and
  `siteEquivSectionIso_apply_section`: the chain-level identification acts on a local
  homogeneous cochain by transporting it along the equivalence of slices. This pins the
  comparison down rather than merely asserting that some isomorphism exists.
* `AlgebraicGeometry.RingedSite.siteEquivSheafHomComplexIso_natural`: the chain-level transport
  is natural in both variables, i.e. it intertwines the maps
  `AlgebraicGeometry.RingedSite.homMap` of internal Hom complexes.

## Implementation notes

The internal Hom complex is available only through the characterising data of
`AlgebraicGeometry.RingedSite.SheafHomComplex`, so the comparison is built on sections: over an
object `W` of `C` the sections of `φ_* SheafHom^•(A, B)` are the sections of `SheafHom^•(A, B)`
over `e(W)`, which are the cochains from `A|_{e(W)}` to `B|_{e(W)}` on `D/e(W)`; the equivalence
of slices `C/W ≌ D/e(W)` carries those to the cochains from `(φ_* A)|_W` to `(φ_* B)|_W`, which
are the sections of `SheafHom^•(φ_* A, φ_* B)` over `W`. The middle step is
`homComplexMapIso` applied to the slice-level equivalence
`Stacks.SheafOfModules.InternalHom.siteEquivModulesOver`, and no comparison of the two restricted
complexes is needed: the localized structure maps are `φ` and `ψ` whiskered along the slice
projections, which makes the transport of `A|_{e(W)}` *equal* to `(φ_* A)|_W`.

Two further compatibilities are what make the identification a map of sheaves of modules and not
merely of sheaves of abelian groups, and they are the only places the hypotheses on `φ` are
used. Linearity over `O_C(W)` — through which the sections of the transport are an
`O_C(W)`-module — is the `smul_natural` field of the two realizations together with the
naturality of `φ`, recorded as `phi_naturality_apply`. Compatibility with restriction along an
arrow of `C` is the `restrict_natural` field of the two realizations together with
`e(h ≫ g) = e(h) ≫ e(g)`; the two slice objects that identifies carry the element being
evaluated in their types, so the substitution is made by `subst` in
`siteEquivSectionIso_apply_section_of_eq` rather than by `congrArg`.

The derived statement needs no descent through a localization. A representative `N` of `K` and
the chosen K-injective resolution `I` of a representative of `L` are enough: there both sides
are the class of an ordinary internal Hom complex by
`AlgebraicGeometry.RingedSite.derivedSheafHomComparison`, and the comparison is the class of the
chain-level transport. That the transport of `I` is still K-injective is [Stacks, Tag 08BJ] in
the form `CochainComplex.isKInjective_mapHomologicalComplex_of_exact`, applied to the adjunction
`ψ_* ⊣ φ_*` of the equivalence, whose left adjoint is exact.

The exactness of `φ_*` is an instance *hypothesis* of the derived section rather than an
instance: the witness is that `φ_*` is the functor of `modulesEquiv`, which needs `ψ`, `H₁` and
`H₂`, and typeclass synthesis cannot recover those from a statement mentioning only `φ`.
`pushforward_preservesFiniteLimits` and `pushforward_preservesFiniteColimits` discharge the
hypotheses; this is the device used for the same reason in
`Stacks.SheafOfModules.derivedOverFunctorEquiv`.

Several functors are made `implicit_reducible` locally, as in
`StacksFrontier/CategoryTheory/Sites/Cohomology/InternalHom/DerivedHomRestriction.lean`: the
sections of `φ_* M` over `W` and the sections of `M` over `e(W)` are the same object only after
the pushforward of presheaves of modules and its restriction of scalars are unfolded, which is
invisible at the transparency a rewrite uses.

## References

* [Stacks Project, Tag 08JB](https://stacks.math.columbia.edu/tag/08JB)
* [Stacks Project, Tag 0E8H](https://stacks.math.columbia.edu/tag/0E8H)
* [Stacks Project, Tag 0A8X](https://stacks.math.columbia.edu/tag/0A8X)
* [Stacks Project, Tag 08BJ](https://stacks.math.columbia.edu/tag/08BJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.RingedSite

universe u v

/-- A fully faithful additive functor preserves the Hom complex of two cochain complexes:
a cochain is carried to the cochain of its images, and the inverse takes preimages. -/
def homComplexMapIso {C D : Type*} [Category.{v} C] [Category.{v} D]
    [Preadditive C] [Preadditive D] (F : C ⥤ D) [F.Additive] [F.Full] [F.Faithful]
    (P I : CochainComplex C ℤ) :
    P.HomComplex I ≅
      CochainComplex.HomComplex ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) := by
  let e (n : ℤ) : CochainComplex.HomComplex.Cochain P I n ≃+
      CochainComplex.HomComplex.Cochain
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) n :=
    { toFun := fun z => z.map F
      invFun := fun z => CochainComplex.HomComplex.Cochain.mk
        (fun p q hpq => F.preimage (z.v p q hpq))
      left_inv := by intro z; ext p q hpq; simp
      right_inv := by intro z; ext p q hpq; simp
      map_add' := fun z w => CochainComplex.HomComplex.Cochain.map_add z w F }
  refine HomologicalComplex.Hom.isoOfComponents (fun n => (e n).toAddCommGrpIso) ?_
  intro i j hij
  ext z
  exact CochainComplex.HomComplex.δ_map i j z F

/-- `homComplexMapIso` applies the functor to a cochain. -/
theorem homComplexMapIso_apply {C D : Type*} [Category.{v} C] [Category.{v} D]
    [Preadditive C] [Preadditive D] (F : C ⥤ D) [F.Additive] [F.Full] [F.Faithful]
    (P I : CochainComplex C ℤ) (n : ℤ) (z : CochainComplex.HomComplex.Cochain P I n) :
    AddCommGrpCat.Hom.hom ((homComplexMapIso F P I).hom.f n) z = z.map F := rfl

/-- Two sections of a degree of an internal Hom complex agree as soon as every local
homogeneous component of the corresponding cochains agrees. -/
theorem sheafHomSection_ext {Z : RingedSite.{u, u, u}}
    {A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) ℤ}
    (H : SheafHomComplex Z A B) (V : Z.C) (n : ℤ)
    {s t : (H.obj.X n).val.obj (op V)}
    (h : ∀ p q (hpq : p + n = q) (W : (Over V)ᵒᵖ)
      (x : ((restrictComplex Z A V).X p).val.obj W),
      (((AddCommGrpCat.Hom.hom ((H.sectionsIso V).hom.f n) s).v p q hpq).val.app W x) =
        (((AddCommGrpCat.Hom.hom ((H.sectionsIso V).hom.f n) t).v p q hpq).val.app W x)) :
    s = t := by
  have he : AddCommGrpCat.Hom.hom ((H.sectionsIso V).hom.f n) s =
      AddCommGrpCat.Hom.hom ((H.sectionsIso V).hom.f n) t := by
    apply CochainComplex.HomComplex.Cochain.ext
    intro p q hpq
    ext W x
    exact h p q hpq W x
  have hi := Iso.hom_inv_id_apply ((HomologicalComplex.eval _ _ n).mapIso (H.sectionsIso V))
  exact (hi s).symm.trans
    ((congrArg (fun z => AddCommGrpCat.Hom.hom ((H.sectionsIso V).inv.f n) z) he).trans (hi t))

/-- Two sections of a degree of an internal Hom complex agree as soon as the corresponding
cochains have the same local homogeneous components. -/
theorem sheafHomSection_ext_v {Z : RingedSite.{u, u, u}}
    {A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) ℤ}
    (H : SheafHomComplex Z A B) (V : Z.C) (n : ℤ)
    {s t : (H.obj.X n).val.obj (op V)}
    (h : ∀ p q (hpq : p + n = q),
      (AddCommGrpCat.Hom.hom ((H.sectionsIso V).hom.f n) s).v p q hpq =
        (AddCommGrpCat.Hom.hom ((H.sectionsIso V).hom.f n) t).v p q hpq) :
    s = t := by
  apply sheafHomSection_ext H V n
  intro p q hpq W x
  exact congrArg (fun m => (m.val.app W) x) (h p q hpq)

attribute [local implicit_reducible]
  CategoryTheory.sheafCompose
  CategoryTheory.Functor.sheafPushforwardContinuous
  ModuleCat.restrictScalars
  ModuleCat.RestrictScalars.obj'
  PresheafOfModules.pushforward
  PresheafOfModules.pushforward₀
  PresheafOfModules.pushforward₀Obj
  PresheafOfModules.presheaf
  PresheafOfModules.toPresheaf
  PresheafOfModules.restrictScalars
  PresheafOfModules.restrictScalarsObj
  SheafOfModules.pushforward
  SheafOfModules.overFunctor
  SheafOfModules.toSheaf
  SheafOfModules.forget

variable {X Y : RingedSite.{u, u, u}} (eqv : Y.C ≌ X.C)
  [eqv.functor.IsContinuous Y.J X.J] [eqv.inverse.IsContinuous X.J Y.J]
  (φ : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⟶
    (eqv.functor.sheafPushforwardContinuous RingCat.{u} Y.J X.J).obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
  (ψ : (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⟶
    (eqv.inverse.sheafPushforwardContinuous RingCat.{u} X.J Y.J).obj
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
  (H₁ : Functor.whiskerRight (NatTrans.op eqv.counit)
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj =
    ψ.hom ≫ eqv.inverse.op.whiskerLeft φ.hom)
  (H₂ : φ.hom ≫ eqv.functor.op.whiskerLeft ψ.hom ≫
    Functor.whiskerRight (NatTrans.op eqv.unit) (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj =
      𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj)

/-- Transport of complexes of modules along the equivalence of ringed sites. -/
abbrev pushComplex :
    CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ ⥤
    CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ :=
  (SheafOfModules.pushforward.{u} φ).mapHomologicalComplex (ComplexShape.up ℤ)

/-- Transport of sheaves of modules on the slice over `W`, along the equivalence of slices. -/
abbrev sliceFunctor (W : Y.C) :
    SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (eqv.functor.obj W)) ⥤
      SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).over W) :=
  (Stacks.SheafOfModules.InternalHom.siteEquivModulesOver.{u, u, u, u} eqv φ ψ H₁ H₂ W).functor

/-- The transport functor on slices is additive. -/
instance sliceFunctor_additive (W : Y.C) : (sliceFunctor eqv φ ψ H₁ H₂ W).Additive where
  map_add := by intros; rfl

/-- The transport functor on slices is an equivalence of categories. -/
instance sliceFunctor_isEquivalence (W : Y.C) :
    (sliceFunctor eqv φ ψ H₁ H₂ W).IsEquivalence :=
  (Stacks.SheafOfModules.InternalHom.siteEquivModulesOver.{u, u, u, u}
    eqv φ ψ H₁ H₂ W).isEquivalence_functor

section

variable (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)

/-- The complex of sections over `W` of the transported internal Hom complex is the
internal Hom complex of the transports: the sections of the transport over `W` are the
sections over `e(W)`, which are the cochains on the slice over `e(W)`, and the equivalence
of slices carries those to the cochains on the slice over `W`. -/
def siteEquivSectionIso (W : Y.C) :
    sectionComplex X (sheafHomComplex X A B).obj (eqv.functor.obj W) ≅
      sectionComplex Y (sheafHomComplex Y ((pushComplex eqv φ).obj A)
        ((pushComplex eqv φ).obj B)).obj W :=
  (sheafHomComplex X A B).sectionsIso (eqv.functor.obj W) ≪≫
    homComplexMapIso (sliceFunctor eqv φ ψ H₁ H₂ W) _ _ ≪≫
    ((sheafHomComplex Y ((pushComplex eqv φ).obj A)
      ((pushComplex eqv φ).obj B)).sectionsIso W).symm

/-- On cochains, `siteEquivSectionIso` transports each local homogeneous component along the
equivalence of slices. -/
theorem siteEquivSectionIso_apply (W : Y.C) (n p q : ℤ) (hpq : p + n = q)
    (s : ((sheafHomComplex X A B).obj.X n).val.obj (op (eqv.functor.obj W))) :
    (AddCommGrpCat.Hom.hom
      (((sheafHomComplex Y ((pushComplex eqv φ).obj A)
        ((pushComplex eqv φ).obj B)).sectionsIso W).hom.f n)
      (AddCommGrpCat.Hom.hom
        ((siteEquivSectionIso eqv φ ψ H₁ H₂ A B W).hom.f n) s)).v p q hpq =
    (sliceFunctor eqv φ ψ H₁ H₂ W).map
      ((AddCommGrpCat.Hom.hom
        (((sheafHomComplex X A B).sectionsIso (eqv.functor.obj W)).hom.f n) s).v p q hpq) := by
  have h := Iso.inv_hom_id_apply
    ((HomologicalComplex.eval _ _ n).mapIso
      ((sheafHomComplex Y ((pushComplex eqv φ).obj A)
        ((pushComplex eqv φ).obj B)).sectionsIso W))
    ((AddCommGrpCat.Hom.hom
      (((sheafHomComplex X A B).sectionsIso (eqv.functor.obj W)).hom.f n) s).map
        (sliceFunctor eqv φ ψ H₁ H₂ W))
  exact congrArg (fun z => z.v p q hpq) h

/-- `siteEquivSectionIso` evaluated on a section of the source complex over a slice object:
the local homogeneous component is the one of the original cochain, read at the image slice
object. -/
theorem siteEquivSectionIso_apply_section (W : Y.C) (n p q : ℤ) (hpq : p + n = q)
    (s : ((sheafHomComplex X A B).obj.X n).val.obj (op (eqv.functor.obj W)))
    {Z : Y.C} (g : Z ⟶ W)
    (x : ((((pushComplex eqv φ).obj A).X p).val.obj (op Z))) :
    ((AddCommGrpCat.Hom.hom
      (((sheafHomComplex Y ((pushComplex eqv φ).obj A)
        ((pushComplex eqv φ).obj B)).sectionsIso W).hom.f n)
      (AddCommGrpCat.Hom.hom
        ((siteEquivSectionIso eqv φ ψ H₁ H₂ A B W).hom.f n) s)).v p q hpq).val.app
          (op (Over.mk g)) x =
    ((AddCommGrpCat.Hom.hom
      (((sheafHomComplex X A B).sectionsIso (eqv.functor.obj W)).hom.f n) s).v
        p q hpq).val.app (op (Over.mk (eqv.functor.map g))) x := by
  rw [siteEquivSectionIso_apply]
  rfl

/-- `siteEquivSectionIso_apply_section` with the slice object on the source site presented by
any morphism equal to the image of `g`. Stated separately because the element being evaluated
has a type mentioning that morphism, so the substitution cannot be made by `congrArg`. -/
theorem siteEquivSectionIso_apply_section_of_eq (W : Y.C) (n p q : ℤ) (hpq : p + n = q)
    (s : ((sheafHomComplex X A B).obj.X n).val.obj (op (eqv.functor.obj W)))
    {Z : Y.C} (g : Z ⟶ W) (m : eqv.functor.obj Z ⟶ eqv.functor.obj W)
    (hm : m = eqv.functor.map g)
    (x : ((((pushComplex eqv φ).obj A).X p).val.obj (op Z))) :
    ((AddCommGrpCat.Hom.hom
      (((sheafHomComplex Y ((pushComplex eqv φ).obj A)
        ((pushComplex eqv φ).obj B)).sectionsIso W).hom.f n)
      (AddCommGrpCat.Hom.hom
        ((siteEquivSectionIso eqv φ ψ H₁ H₂ A B W).hom.f n) s)).v p q hpq).val.app
          (op (Over.mk g)) x =
    ((AddCommGrpCat.Hom.hom
      (((sheafHomComplex X A B).sectionsIso (eqv.functor.obj W)).hom.f n) s).v
        p q hpq).val.app (op (Over.mk m)) x := by
  subst hm
  exact siteEquivSectionIso_apply_section eqv φ ψ H₁ H₂ A B W n p q hpq s g x

omit [eqv.inverse.IsContinuous X.J Y.J] in
/-- The structure map `φ` is natural: restricting a section of `O_Y` along `g` and pushing it
forward is pushing it forward and restricting along the image of `g`. -/
theorem phi_naturality_apply {Z W : Y.C} (g : Z ⟶ W)
    (r : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj (op W)) :
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map (eqv.functor.map g).op
        (φ.hom.app (op W) r) =
      φ.hom.app (op Z) ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.map g.op r) :=
  (congrArg (fun m => (RingCat.Hom.hom m) r) (φ.hom.naturality g.op)).symm

/-- `siteEquivSectionIso` is linear for the action of the structure sheaf of `Y`, the source
being a module over it through the structure map `φ`. -/
def siteEquivSectionLinearEquiv (W : Y.C) (n : ℤ) :
    ((((pushComplex eqv φ).obj (sheafHomComplex X A B).obj).X n).val.obj (op W))
        ≃ₗ[(Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj (op W)]
      (((sheafHomComplex Y ((pushComplex eqv φ).obj A)
        ((pushComplex eqv φ).obj B)).obj.X n).val.obj (op W)) where
  toFun := AddCommGrpCat.Hom.hom ((siteEquivSectionIso eqv φ ψ H₁ H₂ A B W).hom.f n)
  invFun := AddCommGrpCat.Hom.hom ((siteEquivSectionIso eqv φ ψ H₁ H₂ A B W).inv.f n)
  left_inv := Iso.hom_inv_id_apply ((HomologicalComplex.eval _ _ n).mapIso
    (siteEquivSectionIso eqv φ ψ H₁ H₂ A B W))
  right_inv := Iso.inv_hom_id_apply ((HomologicalComplex.eval _ _ n).mapIso
    (siteEquivSectionIso eqv φ ψ H₁ H₂ A B W))
  map_add' := map_add _
  map_smul' r s := by
    apply sheafHomSection_ext (sheafHomComplex Y ((pushComplex eqv φ).obj A)
      ((pushComplex eqv φ).obj B)) W n
    intro p q hpq T x
    obtain ⟨T⟩ := T
    obtain ⟨Z, g, rfl⟩ := Over.mk_surjective T
    simp only [RingHom.id_apply]
    rw [siteEquivSectionIso_apply_section eqv φ ψ H₁ H₂ A B W n p q hpq (r • s) g x]
    rw [(sheafHomComplex Y ((pushComplex eqv φ).obj A)
      ((pushComplex eqv φ).obj B)).smul_natural W r n p q hpq _ g x]
    rw [siteEquivSectionIso_apply_section eqv φ ψ H₁ H₂ A B W n p q hpq s g x]
    refine Eq.trans ((sheafHomComplex X A B).smul_natural (eqv.functor.obj W)
      (φ.hom.app (op W) r) n p q hpq s (eqv.functor.map g) x) ?_
    rw [phi_naturality_apply eqv φ g r]
    rfl

/-- `siteEquivSectionLinearEquiv` is compatible with restriction along an arrow of `Y`. -/
theorem siteEquivSectionLinearEquiv_natural (n : ℤ) {Z W : Y.C} (g : Z ⟶ W)
    (s : ((((pushComplex eqv φ).obj (sheafHomComplex X A B).obj).X n).val.obj (op W))) :
    siteEquivSectionLinearEquiv eqv φ ψ H₁ H₂ A B Z n
        ((((pushComplex eqv φ).obj (sheafHomComplex X A B).obj).X n).val.map g.op s) =
      (((sheafHomComplex Y ((pushComplex eqv φ).obj A)
        ((pushComplex eqv φ).obj B)).obj.X n).val.map g.op)
        (siteEquivSectionLinearEquiv eqv φ ψ H₁ H₂ A B W n s) := by
  apply sheafHomSection_ext (sheafHomComplex Y ((pushComplex eqv φ).obj A)
    ((pushComplex eqv φ).obj B)) Z n
  intro p q hpq T x
  obtain ⟨T⟩ := T
  obtain ⟨Z', h, rfl⟩ := Over.mk_surjective T
  have hLHS := siteEquivSectionIso_apply_section eqv φ ψ H₁ H₂ A B Z n p q hpq
    ((((pushComplex eqv φ).obj (sheafHomComplex X A B).obj).X n).val.map g.op s) h x
  have hX := (sheafHomComplex X A B).restrict_natural (eqv.functor.map g) n p q hpq s
    (eqv.functor.map h) x
  have hW := siteEquivSectionIso_apply_section_of_eq eqv φ ψ H₁ H₂ A B W n p q hpq s (h ≫ g)
    (eqv.functor.map h ≫ eqv.functor.map g) (eqv.functor.map_comp h g).symm x
  have hY := (sheafHomComplex Y ((pushComplex eqv φ).obj A)
    ((pushComplex eqv φ).obj B)).restrict_natural g n p q hpq
      (AddCommGrpCat.Hom.hom
        ((siteEquivSectionIso eqv φ ψ H₁ H₂ A B W).hom.f n) s) h x
  exact hLHS.trans (hX.symm.trans (hW.symm.trans hY))

/-- **The internal Hom complex is invariant under an equivalence of ringed sites.** The
transport along the equivalence of the internal Hom complex `SheafHom(A, B)` is the internal
Hom complex of the transports.

This is the chain-level form of the invariance of the derived internal Hom; its degreewise
identification on sections is `siteEquivSectionIso`, which on each local homogeneous component
is the transport of a local morphism along the equivalence of slices, and
`siteEquivSheafHomComplexIso_natural` is its naturality in both variables. -/
def siteEquivSheafHomComplexIso :
    (pushComplex eqv φ).obj (sheafHomComplex X A B).obj ≅
      (sheafHomComplex Y ((pushComplex eqv φ).obj A) ((pushComplex eqv φ).obj B)).obj := by
  let e (n : ℤ) :
      (((pushComplex eqv φ).obj (sheafHomComplex X A B).obj).X n).val ≅
        ((sheafHomComplex Y ((pushComplex eqv φ).obj A)
          ((pushComplex eqv φ).obj B)).obj.X n).val :=
    PresheafOfModules.isoMk
      (fun W => (siteEquivSectionLinearEquiv eqv φ ψ H₁ H₂ A B W.unop n).toModuleIso)
      (by
        intro W Z f
        ext s
        exact siteEquivSectionLinearEquiv_natural eqv φ ψ H₁ H₂ A B n f.unop s)
  refine HomologicalComplex.Hom.isoOfComponents
    (fun n => (SheafOfModules.fullyFaithfulForget _).preimageIso (e n)) ?_
  intro i j hij
  ext W s
  exact ConcreteCategory.congr_hom
    ((siteEquivSectionIso eqv φ ψ H₁ H₂ A B W.unop).hom.comm i j) s

end

/-- **The chain-level transport is natural in both variables.** Transporting the map of
internal Hom complexes induced by `f : A' ⟶ A` and `g : B ⟶ B'` along the equivalence is,
through `siteEquivSheafHomComplexIso`, the map of internal Hom complexes on `Y` induced by the
transports of `f` and `g`. -/
theorem siteEquivSheafHomComplexIso_natural
    {A A' B B' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (f : A' ⟶ A) (g : B ⟶ B') :
    (pushComplex eqv φ).map (homMap X f g) ≫
        (siteEquivSheafHomComplexIso eqv φ ψ H₁ H₂ A' B').hom =
      (siteEquivSheafHomComplexIso eqv φ ψ H₁ H₂ A B).hom ≫
        homMap Y ((pushComplex eqv φ).map f) ((pushComplex eqv φ).map g) := by
  ext n V s
  apply sheafHomSection_ext_v (sheafHomComplex Y ((pushComplex eqv φ).obj A')
    ((pushComplex eqv φ).obj B')) V.unop n
  intro p q hpq
  change (AddCommGrpCat.Hom.hom
      (((sheafHomComplex Y ((pushComplex eqv φ).obj A')
        ((pushComplex eqv φ).obj B')).sectionsIso V.unop).hom.f n)
      (AddCommGrpCat.Hom.hom
        ((siteEquivSectionIso eqv φ ψ H₁ H₂ A' B' V.unop).hom.f n)
        (((homMap X f g).f n).val.app (op (eqv.functor.obj V.unop)) s))).v p q hpq =
    (AddCommGrpCat.Hom.hom
      (((sheafHomComplex Y ((pushComplex eqv φ).obj A')
        ((pushComplex eqv φ).obj B')).sectionsIso V.unop).hom.f n)
      (((homMap Y ((pushComplex eqv φ).map f) ((pushComplex eqv φ).map g)).f n).val.app
        (op V.unop)
        (AddCommGrpCat.Hom.hom
          ((siteEquivSectionIso eqv φ ψ H₁ H₂ A B V.unop).hom.f n) s))).v p q hpq
  rw [siteEquivSectionIso_apply eqv φ ψ H₁ H₂ A' B' V.unop n p q hpq
    (((homMap X f g).f n).val.app (op (eqv.functor.obj V.unop)) s)]
  rw [sectionsIso_homMap_v X f g (eqv.functor.obj V.unop) n p q hpq s]
  rw [sectionsIso_homMap_v Y ((pushComplex eqv φ).map f) ((pushComplex eqv φ).map g)
    V.unop n p q hpq (AddCommGrpCat.Hom.hom
      ((siteEquivSectionIso eqv φ ψ H₁ H₂ A B V.unop).hom.f n) s)]
  rw [siteEquivSectionIso_apply eqv φ ψ H₁ H₂ A B V.unop n p q hpq s]
  simp only [Functor.map_comp]
  rfl

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- The equivalence of categories of sheaves of modules underlying the equivalence of ringed
sites: the two pushforwards along the structure maps are mutually inverse. -/
abbrev modulesEquiv : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ≌
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) :=
  SheafOfModules.pushforwardPushforwardEquivalence eqv φ ψ H₁ H₂

/-- The pushforward of sheaves of modules along `φ` is additive. -/
instance pushforward_additive : (SheafOfModules.pushforward.{u} φ).Additive where
  map_add := by intros; rfl

include φ ψ H₁ H₂ in
/-- The pushforward along `φ` is the equivalence of `modulesEquiv`, hence exact. -/
theorem pushforward_preservesFiniteLimits :
    PreservesFiniteLimits (SheafOfModules.pushforward.{u} φ) :=
  inferInstanceAs (PreservesFiniteLimits (modulesEquiv eqv φ ψ H₁ H₂).functor)

include φ ψ H₁ H₂ in
/-- The pushforward along `φ` preserves finite colimits; see
`pushforward_preservesFiniteLimits`. -/
theorem pushforward_preservesFiniteColimits :
    PreservesFiniteColimits (SheafOfModules.pushforward.{u} φ) :=
  inferInstanceAs (PreservesFiniteColimits (modulesEquiv eqv φ ψ H₁ H₂).functor)

include φ ψ H₁ H₂ in
/-- The pushforward along `ψ`, the inverse of the equivalence, preserves finite limits. -/
theorem pushforward_inverse_preservesFiniteLimits :
    PreservesFiniteLimits (SheafOfModules.pushforward.{u} ψ) :=
  inferInstanceAs (PreservesFiniteLimits (modulesEquiv eqv φ ψ H₁ H₂).inverse)

include φ ψ H₁ H₂ in
/-- The pushforward along `ψ`, the inverse of the equivalence, preserves finite colimits. -/
theorem pushforward_inverse_preservesFiniteColimits :
    PreservesFiniteColimits (SheafOfModules.pushforward.{u} ψ) :=
  inferInstanceAs (PreservesFiniteColimits (modulesEquiv eqv φ ψ H₁ H₂).inverse)

variable [hlim : PreservesFiniteLimits (SheafOfModules.pushforward.{u} φ)]
  [hcolim : PreservesFiniteColimits (SheafOfModules.pushforward.{u} φ)]

/-- **The derived internal Hom is invariant under an equivalence of ringed sites.** The
transport along the equivalence of `RSheafHom_{O_X}(K, L)` is the derived internal Hom of the
transports of `K` and `L`.

A representative `N` of `K` and a K-injective representative `I` of `L` are chosen; there both
sides are the class of an ordinary internal Hom complex, by
`AlgebraicGeometry.RingedSite.derivedSheafHomComparison`, and the comparison is the class of
the chain-level transport `siteEquivSheafHomComplexIso`. The transport of `I` stays K-injective
by [Stacks, Tag 08BJ], the inverse of the equivalence being exact. -/
def siteEquivDerivedSheafHomIso
    (K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (SheafOfModules.pushforward.{u} φ).mapDerivedCategory.obj
        (((derivedSheafHomBifunctor X).obj (op K)).obj L) ≅
      ((derivedSheafHomBifunctor Y).obj
        (op ((SheafOfModules.pushforward.{u} φ).mapDerivedCategory.obj K))).obj
          ((SheafOfModules.pushforward.{u} φ).mapDerivedCategory.obj L) := by
  letI := pushforward_inverse_preservesFiniteLimits eqv φ ψ H₁ H₂
  letI := pushforward_inverse_preservesFiniteColimits eqv φ ψ H₁ H₂
  let N := DerivedCategory.Q.objPreimage K
  let eN : DerivedCategory.Q.obj N ≅ K := DerivedCategory.Q.objObjPreimageIso K
  let M₀ := DerivedCategory.Q.objPreimage L
  let I := (kInjectiveResolution X).obj M₀
  letI : I.IsKInjective :=
    Stacks.Injectives.kInjectiveResolutionFunctor_obj_isKInjective
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) M₀
  let eI : DerivedCategory.Q.obj I ≅ L :=
    (asIso (DerivedCategory.Q.map ((kInjectiveAugmentation X).app M₀))).symm ≪≫
      DerivedCategory.Q.objObjPreimageIso L
  letI : ((pushComplex eqv φ).obj I).IsKInjective :=
    CochainComplex.isKInjective_mapHomologicalComplex_of_exact
      (SheafOfModules.pushforward.{u} φ) (SheafOfModules.pushforward.{u} ψ)
      (modulesEquiv eqv φ ψ H₁ H₂).symm.toAdjunction I
  let epN : DerivedCategory.Q.obj ((pushComplex eqv φ).obj N) ≅
      (SheafOfModules.pushforward.{u} φ).mapDerivedCategory.obj K :=
    ((SheafOfModules.pushforward.{u} φ).mapDerivedCategoryFactors.app N).symm ≪≫
      (SheafOfModules.pushforward.{u} φ).mapDerivedCategory.mapIso eN
  let epI : DerivedCategory.Q.obj ((pushComplex eqv φ).obj I) ≅
      (SheafOfModules.pushforward.{u} φ).mapDerivedCategory.obj L :=
    ((SheafOfModules.pushforward.{u} φ).mapDerivedCategoryFactors.app I).symm ≪≫
      (SheafOfModules.pushforward.{u} φ).mapDerivedCategory.mapIso eI
  exact (SheafOfModules.pushforward.{u} φ).mapDerivedCategory.mapIso
      (derivedSheafHomObjectsModelIso X eN eI ≪≫ derivedSheafHomComparison X N I) ≪≫
    (SheafOfModules.pushforward.{u} φ).mapDerivedCategoryFactors.app
      (sheafHomComplex X N I).obj ≪≫
    DerivedCategory.Q.mapIso (siteEquivSheafHomComplexIso eqv φ ψ H₁ H₂ N I) ≪≫
    (derivedSheafHomComparison Y ((pushComplex eqv φ).obj N)
      ((pushComplex eqv φ).obj I)).symm ≪≫
    (derivedSheafHomObjectsModelIso Y epN epI).symm

end Derived

section OfIso

attribute [local instance] HasDerivedCategory.standard

variable [hφ : IsIso φ]

/-- **The chain-level transport, for an invertible structure map.** This is
`siteEquivSheafHomComplexIso` with the inverse structure map and the two compatibilities
supplied by `Stacks.SheafOfModules.InternalHom.psiOfIso`, so that only `φ` and its
invertibility are needed.

The invertibility hypothesis is the *named* instance argument `hφ`, so that it can be passed by
hand: the two interchangeable `Category` instances of `CategoryTheory.Sheaf` keep synthesis from
finding it at a use site. -/
def siteEquivSheafHomComplexIsoOfIso
    (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    (pushComplex eqv φ).obj (sheafHomComplex X A B).obj ≅
      (sheafHomComplex Y ((pushComplex eqv φ).obj A) ((pushComplex eqv φ).obj B)).obj :=
  siteEquivSheafHomComplexIso eqv φ (Stacks.SheafOfModules.InternalHom.psiOfIso eqv φ)
    (Stacks.SheafOfModules.InternalHom.psiOfIso_counit eqv φ)
    (Stacks.SheafOfModules.InternalHom.psiOfIso_unit eqv φ) A B

/-- `siteEquivSheafHomComplexIsoOfIso` is natural in both variables. -/
theorem siteEquivSheafHomComplexIsoOfIso_natural
    {A A' B B' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (f : A' ⟶ A) (g : B ⟶ B') :
    (pushComplex eqv φ).map (homMap X f g) ≫
        (siteEquivSheafHomComplexIsoOfIso eqv φ A' B').hom =
      (siteEquivSheafHomComplexIsoOfIso eqv φ A B).hom ≫
        homMap Y ((pushComplex eqv φ).map f) ((pushComplex eqv φ).map g) :=
  siteEquivSheafHomComplexIso_natural eqv φ _ _ _ f g

/-- The pushforward along an invertible `φ` preserves finite limits. -/
theorem pushforward_preservesFiniteLimitsOfIso :
    PreservesFiniteLimits (SheafOfModules.pushforward.{u} φ) :=
  pushforward_preservesFiniteLimits eqv φ (Stacks.SheafOfModules.InternalHom.psiOfIso eqv φ)
    (Stacks.SheafOfModules.InternalHom.psiOfIso_counit eqv φ)
    (Stacks.SheafOfModules.InternalHom.psiOfIso_unit eqv φ)

/-- The pushforward along an invertible `φ` preserves finite colimits. -/
theorem pushforward_preservesFiniteColimitsOfIso :
    PreservesFiniteColimits (SheafOfModules.pushforward.{u} φ) :=
  pushforward_preservesFiniteColimits eqv φ (Stacks.SheafOfModules.InternalHom.psiOfIso eqv φ)
    (Stacks.SheafOfModules.InternalHom.psiOfIso_counit eqv φ)
    (Stacks.SheafOfModules.InternalHom.psiOfIso_unit eqv φ)

variable [hlim : PreservesFiniteLimits (SheafOfModules.pushforward.{u} φ)]
  [hcolim : PreservesFiniteColimits (SheafOfModules.pushforward.{u} φ)]

/-- **The derived-level transport, for an invertible structure map.** See
`siteEquivSheafHomComplexIsoOfIso` for why the invertibility is a named instance argument. -/
def siteEquivDerivedSheafHomIsoOfIso
    (K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (SheafOfModules.pushforward.{u} φ).mapDerivedCategory.obj
        (((derivedSheafHomBifunctor X).obj (op K)).obj L) ≅
      ((derivedSheafHomBifunctor Y).obj
        (op ((SheafOfModules.pushforward.{u} φ).mapDerivedCategory.obj K))).obj
          ((SheafOfModules.pushforward.{u} φ).mapDerivedCategory.obj L) :=
  siteEquivDerivedSheafHomIso eqv φ (Stacks.SheafOfModules.InternalHom.psiOfIso eqv φ)
    (Stacks.SheafOfModules.InternalHom.psiOfIso_counit eqv φ)
    (Stacks.SheafOfModules.InternalHom.psiOfIso_unit eqv φ) K L

end OfIso

end AlgebraicGeometry.RingedSite

end
