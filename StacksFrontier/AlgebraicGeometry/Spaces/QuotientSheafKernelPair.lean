module

public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import StacksFrontier.AlgebraicGeometry.Spaces.PresentationFromQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafLocalRelation
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Continuous

/-!
# A relation is the kernel pair of the projection onto its quotient sheaf

Let `j : R ⟶ U ×_S U` be an internal equivalence relation of schemes over `S` and let
`F : C ⥤ Over S` restrict the functor of points to a site `C`.  The relation is the kernel
pair of the projection of `U` onto the quotient **presheaf**
(`AlgebraicGeometry.Space.quotientPresheaf_isPullback`), because over each test object the
quotient presheaf is a pointwise quotient of sets.  If the functors of points of `R` and of
`U` are already sheaves on `C`, the projection onto the quotient *sheaf* has the same kernel
pair (`Stacks.Groupoids.isPullback_toQuotientSheaf_self`): sheafification is a left exact
localization and the two outer objects of the square are unchanged by it.

No algebraicity hypothesis on the quotient is needed.  This distinguishes the statement from
`AlgebraicGeometry.Space.quotientMap_isPullback`, which is about the Yoneda spelling of the
same projection on the big fppf site and assumes that the quotient is an algebraic space in
order to produce the representable kernel pair of Stacks 02WV.

## Main results

* `AlgebraicGeometry.Space.isPullback_toQuotientSheaf_bigFppf`: the same on the big fppf
  site of `S`, where the two sheaf conditions hold for every scheme over `S` by continuity of
  the inclusion of the site.
* `Stacks.Sites.isPullback_of_locallyRelated`: the same kernel-pair property for two jointly
  injective maps of presheaves of sets on an arbitrary site, assembled from its universal
  property rather than from sheafification, and `Stacks.Sites.existsUnique_of_locallyRelated`
  the unique local section it is built out of.
* `Stacks.Groupoids.isPullback_yoneda_of_locallyRelated`: its form for two jointly monic
  morphisms of the site itself, and `AlgebraicGeometry.Space.isPullback_of_locallyRelated` the
  form on the big fppf site of `S`, where the two sheaf conditions are free, the topology being
  subcanonical.
* `Stacks.Groupoids.exists_cover_rel_of_toQuotientSheaf_apply_eq`: Stacks 045Y, (1) implies
  (2), for a site whose universes are unrelated to those of the presheaves of points.
* `Stacks.Sites.eq_of_mono_prodLift`: two morphisms into the relation which agree after
  composing with each of two jointly monic morphisms out of it are equal.
* `Stacks.Groupoids.pointsIsoYoneda`: for a fully faithful `G`, the functor of points of
  `G.obj X` restricted along `G` is the presheaf represented by `X`.

## Implementation notes

The sheaf conditions are discharged on the big fppf site by
`AlgebraicGeometry.BigFppfOver.isSheaf_post_inclusion_op_comp_yoneda_obj`, which holds for an
arbitrary `S`-scheme and not only for an object of the size-bounded site; so the relation
scheme is not required to lie in the site.

`Stacks.Sites.isPullback_of_locallyRelated` takes a different route to the same conclusion, and
it is the one that applies when the quotient is not given as a sheafification: the pullback
square is produced from its universal property, so no pointwise description of limits in a
category of presheaves is needed. The lifted map is assembled componentwise out of the unique
sections of `Stacks.Sites.existsUnique_of_locallyRelated`, and its naturality as well as the
uniqueness clause of the universal property are both instances of that uniqueness. Joint
injectivity of the two maps is taken as a pointwise hypothesis rather than as monicity of a map
into a product, so that the statement applies to sites with no binary products;
`Stacks.Sites.eq_of_mono_prodLift` derives it from monicity where products do exist.

`Stacks.Groupoids.relSieve_mem_of_toQuotientSheaf_apply_eq` constrains the site to `C : Type u`
with `Category.{u} C`, that being the shape in which
`CategoryTheory.Presheaf.isLocallyInjective_toSheafify` is stated for presheaves of types.
`Stacks.Groupoids.exists_cover_rel_of_toQuotientSheaf_apply_eq` proves the same thing with
`CategoryTheory.GrothendieckTopology.WEqualsLocallyBijective` in place of that constraint, which
is what carries local injectivity of `CategoryTheory.toSheafify` to a presheaf valued in a
universe unrelated to the site's, and which holds automatically when the two agree. The
constraint matters because `AlgebraicGeometry.BigFppfOver`, a slice of a full subcategory of
`AlgebraicGeometry.Scheme`, is a category of type `Type (u + 1)` with morphisms in `Type u`, and
so does not satisfy it.

## References

* [Stacks Project, Tag 00WQ](https://stacks.math.columbia.edu/tag/00WQ)
* [Stacks Project, Tag 022P](https://stacks.math.columbia.edu/tag/022P)
* [Stacks Project, Tag 02VG](https://stacks.math.columbia.edu/tag/02VG)
* [Stacks Project, Tag 02WV](https://stacks.math.columbia.edu/tag/02WV)
* [Stacks Project, Tag 045Y](https://stacks.math.columbia.edu/tag/045Y)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace Stacks.Sites

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {P Q A : Cᵒᵖ ⥤ Type w} (τ σ : P ⟶ Q) (c : Q ⟶ A)

/-- Two morphisms into `R` which agree after composing with each of two jointly monic morphisms
out of `R` are equal. This is joint injectivity of the two morphisms in the form in which the
statements below use it, derived from monicity of the induced morphism to the product. -/
theorem eq_of_mono_prodLift {R U : C} [HasBinaryProduct U U] (t s : R ⟶ U)
    [Mono (prod.lift t s)] {T : C} {r r' : T ⟶ R} (ht : r ≫ t = r' ≫ t)
    (hs : r ≫ s = r' ≫ s) : r = r' := by
  refine (cancel_mono (prod.lift t s)).1 (prod.hom_ext ?_ ?_)
  · simpa only [Category.assoc, prod.lift_fst] using ht
  · simpa only [Category.assoc, prod.lift_snd] using hs

/-- A section of `P` over `T` whose images under `τ` and `σ` are two prescribed sections `a`, `b`
of `Q` exists and is unique, as soon as `P` and `Q` are sheaves, `τ` and `σ` are jointly
injective, and such a section exists locally on a covering sieve of `T`.

Existence is the amalgamation of the local sections, which are a compatible family precisely
because joint injectivity makes each of them unique; that the amalgamation has the prescribed
images is the separatedness of `Q`. -/
theorem existsUnique_of_locallyRelated
    (hP : Presieve.IsSheaf J P) (hQ : Presieve.IsSheaf J Q)
    (hinj : ∀ ⦃T : Cᵒᵖ⦄ (r r' : P.obj T), τ.app T r = τ.app T r' →
      σ.app T r = σ.app T r' → r = r')
    {T : C} {a b : Q.obj (op T)} (W : Sieve T) (hW : W ∈ J T)
    (hr : ∀ ⦃Y : C⦄ (f : Y ⟶ T), W f →
      ∃ r : P.obj (op Y), τ.app (op Y) r = Q.map f.op a ∧ σ.app (op Y) r = Q.map f.op b) :
    ∃! r : P.obj (op T), τ.app (op T) r = a ∧ σ.app (op T) r = b := by
  classical
  let x : Presieve.FamilyOfElements P (W : Presieve T) := fun _ f hf => (hr f hf).choose
  have hxτ : ∀ ⦃Y : C⦄ (f : Y ⟶ T) (hf : (W : Presieve T) f),
      τ.app (op Y) (x f hf) = Q.map f.op a := fun _ f hf => (hr f hf).choose_spec.1
  have hxσ : ∀ ⦃Y : C⦄ (f : Y ⟶ T) (hf : (W : Presieve T) f),
      σ.app (op Y) (x f hf) = Q.map f.op b := fun _ f hf => (hr f hf).choose_spec.2
  have key : ∀ (ν : P ⟶ Q) (u : Q.obj (op T)),
      (∀ ⦃Y : C⦄ (f : Y ⟶ T) (hf : (W : Presieve T) f),
        ν.app (op Y) (x f hf) = Q.map f.op u) →
      ∀ ⦃Y₁ Y₂ Z : C⦄ (g₁ : Z ⟶ Y₁) (g₂ : Z ⟶ Y₂) ⦃f₁ : Y₁ ⟶ T⦄ ⦃f₂ : Y₂ ⟶ T⦄
        (h₁ : (W : Presieve T) f₁) (h₂ : (W : Presieve T) f₂), g₁ ≫ f₁ = g₂ ≫ f₂ →
        ν.app (op Z) (P.map g₁.op (x f₁ h₁)) = ν.app (op Z) (P.map g₂.op (x f₂ h₂)) := by
    intro ν u hν Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ hg
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply, hν f₁ h₁, hν f₂ h₂,
      ← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp, hg]
  have hxc : x.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ hg
    exact hinj _ _ (key τ a hxτ g₁ g₂ h₁ h₂ hg) (key σ b hxσ g₁ g₂ h₁ h₂ hg)
  have ha : τ.app (op T) ((hP W hW).amalgamate x hxc) = a := by
    refine ((hQ W hW).isSeparatedFor).ext ?_
    intro Y f hf
    rw [← NatTrans.naturality_apply, (hP W hW).valid_glue hxc f hf, hxτ f hf]
  have hb : σ.app (op T) ((hP W hW).amalgamate x hxc) = b := by
    refine ((hQ W hW).isSeparatedFor).ext ?_
    intro Y f hf
    rw [← NatTrans.naturality_apply, (hP W hW).valid_glue hxc f hf, hxσ f hf]
  exact ⟨_, ⟨ha, hb⟩, fun _ h => hinj _ _ (h.1.trans ha.symm) (h.2.trans hb.symm)⟩

/-- **The kernel-pair criterion.** If `P` and `Q` are sheaves, if `τ, σ : P ⟶ Q` are jointly
injective, and if two sections of `Q` with the same image under `c : Q ⟶ A` are locally the
images under `τ` and `σ` of a section of `P`, then the square with sides `τ`, `σ`, `c`, `c` is a
pullback square: `P` represents the kernel pair of `c`.

The lift of a cone is built componentwise from the unique sections of
`Stacks.Sites.existsUnique_of_locallyRelated`; both its naturality and the uniqueness clause of
the universal property are instances of that uniqueness. -/
theorem isPullback_of_locallyRelated
    (hP : Presieve.IsSheaf J P) (hQ : Presieve.IsSheaf J Q)
    (hinj : ∀ ⦃T : Cᵒᵖ⦄ (r r' : P.obj T), τ.app T r = τ.app T r' →
      σ.app T r = σ.app T r' → r = r')
    (hcomm : τ ≫ c = σ ≫ c)
    (hloc : ∀ ⦃T : C⦄ (a b : Q.obj (op T)), c.app (op T) a = c.app (op T) b →
      ∃ W : Sieve T, W ∈ J T ∧ ∀ ⦃Y : C⦄ (f : Y ⟶ T), W f →
        ∃ r : P.obj (op Y), τ.app (op Y) r = Q.map f.op a ∧ σ.app (op Y) r = Q.map f.op b) :
    IsPullback τ σ c c := by
  classical
  have key : ∀ (T : Cᵒᵖ) (a b : Q.obj T), c.app T a = c.app T b →
      ∃! r : P.obj T, τ.app T r = a ∧ σ.app T r = b := by
    rintro ⟨T⟩ a b h
    obtain ⟨W, hW, hr⟩ := hloc a b h
    exact existsUnique_of_locallyRelated J τ σ hP hQ hinj W hW hr
  have hcond : ∀ (s : PullbackCone c c) (T : Cᵒᵖ) (w : s.pt.obj T),
      c.app T (s.fst.app T w) = c.app T (s.snd.app T w) := by
    intro s T w
    have h : (s.fst ≫ c).app T w = (s.snd ≫ c).app T w := by rw [s.condition]
    simpa only [NatTrans.comp_app_apply] using h
  let r (s : PullbackCone c c) (T : Cᵒᵖ) (w : s.pt.obj T) : P.obj T :=
    (key T (s.fst.app T w) (s.snd.app T w) (hcond s T w)).choose
  have hrτ : ∀ (s : PullbackCone c c) (T : Cᵒᵖ) (w : s.pt.obj T),
      τ.app T (r s T w) = s.fst.app T w :=
    fun s T w => (key T _ _ (hcond s T w)).choose_spec.1.1
  have hrσ : ∀ (s : PullbackCone c c) (T : Cᵒᵖ) (w : s.pt.obj T),
      σ.app T (r s T w) = s.snd.app T w :=
    fun s T w => (key T _ _ (hcond s T w)).choose_spec.1.2
  let lft (s : PullbackCone c c) : s.pt ⟶ P :=
    { app := fun T => TypeCat.ofHom (r s T)
      naturality := by
        intro T₁ T₂ f
        ext w
        refine hinj (T := T₂) (r s T₂ (s.pt.map f w)) (P.map f (r s T₁ w)) ?_ ?_
        · rw [hrτ s T₂, NatTrans.naturality_apply, NatTrans.naturality_apply, hrτ s T₁]
        · rw [hrσ s T₂, NatTrans.naturality_apply, NatTrans.naturality_apply, hrσ s T₁] }
  refine IsPullback.of_isLimit' ⟨hcomm⟩ (PullbackCone.IsLimit.mk hcomm lft ?_ ?_ ?_)
  · intro s
    ext T w
    exact hrτ s T w
  · intro s
    ext T w
    exact hrσ s T w
  · intro s m hm₁ hm₂
    ext T w
    have h₁ : τ.app T (m.app T w) = s.fst.app T w := by
      rw [← NatTrans.comp_app_apply, hm₁]
    have h₂ : σ.app T (m.app T w) = s.snd.app T w := by
      rw [← NatTrans.comp_app_apply, hm₂]
    exact (key T _ _ (hcond s T w)).choose_spec.2 _ ⟨h₁, h₂⟩

end Stacks.Sites

namespace Stacks.Groupoids

variable {C : Type u} [Category.{v} C]

/-- **The kernel-pair criterion for a relation in the site.** Let `t, s : R ⟶ U` be two jointly
monic morphisms of a site `(C, J)` whose representable presheaves are sheaves, and let
`c : h_U ⟶ A` coequalize them. If two `T`-points of `U` with the same image under `c` are
locally related by `R`, then `h_R` represents the kernel pair of `c`.

This is the form that applies to a relation in an over-category of the ambient category of a
site of schemes, where the functor of points of an object is its representable presheaf. -/
theorem isPullback_yoneda_of_locallyRelated (J : GrothendieckTopology C) {R U : C} (t s : R ⟶ U)
    {A : Cᵒᵖ ⥤ Type v} (c : yoneda.obj U ⟶ A)
    (hR : Presieve.IsSheaf J (yoneda.obj R)) (hU : Presieve.IsSheaf J (yoneda.obj U))
    (hinj : ∀ ⦃T : C⦄ (r r' : T ⟶ R), r ≫ t = r' ≫ t → r ≫ s = r' ≫ s → r = r')
    (hcomm : yoneda.map t ≫ c = yoneda.map s ≫ c)
    (hloc : ∀ ⦃T : C⦄ (a b : T ⟶ U), c.app (op T) a = c.app (op T) b →
      ∃ W : Sieve T, W ∈ J T ∧ ∀ ⦃Y : C⦄ (f : Y ⟶ T), W f →
        ∃ r : Y ⟶ R, r ≫ t = f ≫ a ∧ r ≫ s = f ≫ b) :
    IsPullback (yoneda.map t) (yoneda.map s) c c := by
  refine Sites.isPullback_of_locallyRelated J _ _ c hR hU ?_ hcomm ?_
  · rintro ⟨T⟩ r r' h₁ h₂
    exact hinj r r' h₁ h₂
  · intro T a b h
    obtain ⟨W, hW, hr⟩ := hloc a b h
    exact ⟨W, hW, hr⟩

/-- **Stacks 045Y, (1) implies (2), at unconstrained universes.** Two `F.obj T`-points of `U`
with the same image in the quotient sheaf of a pre-equivalence relation become related by the
pre-relation on a covering of `T`.

`Stacks.Groupoids.relSieve_mem_of_toQuotientSheaf_apply_eq` is the same statement for a site
`C : Type u` with `Category.{u} C`, that being the shape in which
`CategoryTheory.Presheaf.isLocallyInjective_toSheafify` is stated for presheaves of types. The
hypothesis `CategoryTheory.GrothendieckTopology.WEqualsLocallyBijective` replaces that
constraint: it is exactly what makes `CategoryTheory.toSheafify` locally injective for
presheaves valued in a universe unrelated to the site's, and it holds automatically when the
two universes do agree. -/
theorem exists_cover_rel_of_toQuotientSheaf_apply_eq {S : Scheme.{w}} {C' : Type u}
    [Category.{v} C'] (F : C' ⥤ Over S) {R U : Over S} (j : PreRelation R U)
    (J : GrothendieckTopology C') [HasSheafify J (Type w)]
    [J.WEqualsLocallyBijective (Type w)] (hj : IsPreEquivalenceRelation j) {T : C'}
    (a b : F.obj T ⟶ U)
    (h : (toQuotientSheaf J F j).app (op T) a = (toQuotientSheaf J F j).app (op T) b) :
    ∃ W : Sieve T, W ∈ J T ∧ ∀ ⦃Y : C'⦄ (f : Y ⟶ T), W f →
      ∃ r : F.obj Y ⟶ R, r ≫ j.target = F.map f ≫ a ∧ r ≫ j.source = F.map f ≫ b := by
  have hx : (toSheafify J (quotientPresheaf F j)).app (op T)
      ((toQuotientPresheaf F j).app (op T) a) =
      (toSheafify J (quotientPresheaf F j)).app (op T)
        ((toQuotientPresheaf F j).app (op T) b) := by
    simpa only [toQuotientSheaf, NatTrans.comp_app, ConcreteCategory.comp_apply] using h
  refine ⟨Presheaf.equalizerSieve ((toQuotientPresheaf F j).app (op T) a)
      ((toQuotientPresheaf F j).app (op T) b),
    Presheaf.equalizerSieve_mem J (toSheafify J (quotientPresheaf F j)) _ _ hx, ?_⟩
  intro Y f hf
  have hf' : (toQuotientPresheaf F j).app (op Y) (F.map f ≫ a) =
      (toQuotientPresheaf F j).app (op Y) (F.map f ≫ b) := by
    rw [show F.map f ≫ a = (points F U).map f.op a from rfl,
      show F.map f ≫ b = (points F U).map f.op b from rfl,
      NatTrans.naturality_apply (toQuotientPresheaf F j) f.op a,
      NatTrans.naturality_apply (toQuotientPresheaf F j) f.op b]
    exact hf
  exact rel_of_toQuotientPresheaf_apply_eq F j hj Y hf'

/-- For a fully faithful functor `G : C ⥤ D`, the functor of points of `G.obj X` restricted along
`G` is the presheaf on `C` represented by `X`. This is the comparison between a presheaf on a
site whose objects are schemes over a base and a presheaf on a slice of the site's own ambient
category. -/
@[simps!]
noncomputable def pointsIsoYoneda {D : Type u} [Category.{v} D] (G : C ⥤ D) [G.Full]
    [G.Faithful] (X : C) : G.op ⋙ yoneda.obj (G.obj X) ≅ yoneda.obj X :=
  NatIso.ofComponents
    (fun _ => Equiv.toIso (Functor.FullyFaithful.ofFullyFaithful G).homEquiv.symm)
    (fun f => by
      ext g
      exact (Functor.FullyFaithful.ofFullyFaithful G).map_injective (by simp))

end Stacks.Groupoids

namespace AlgebraicGeometry.Space

open Stacks.Groupoids

/-- On the big fppf site of `S` the relation is always the kernel pair of the projection onto
the quotient sheaf: the functor of points of an arbitrary `S`-scheme is a sheaf there.

This is the unconditional form of the square the clauses `not_separated`, `quasi_separated`
and `locally_separated` of Stacks 03FN consume; it carries no tag of its own because the
tagged statement of Stacks 02WV is about the Yoneda spelling of the quotient map and needs
the quotient to be an algebraic space. -/
theorem isPullback_toQuotientSheaf_bigFppf (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    {R U : Over S} (j : PreRelation R U) [IsEquivalenceRelation j.target j.source] :
    IsPullback (targetMap (Over.post B.inclusion) j) (sourceMap (Over.post B.inclusion) j)
      (toQuotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion) j)
      (toQuotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion) j) :=
  isPullback_toQuotientSheaf_self _ _ j
    (BigFppfOver.isSheaf_post_inclusion_op_comp_yoneda_obj B S hS R)
    (BigFppfOver.isSheaf_post_inclusion_op_comp_yoneda_obj B S hS U)

/-- **The kernel-pair square for a relation in the big fppf category over `S`.** Let
`s, t : R ⟶ U` be two jointly monic morphisms of the big fppf category over `S`, and let
`c : h_U ⟶ F` coequalize them. If two `T`-points of `U` with the same image under `c` become
related by `R` after restriction along a covering, then `h_R` represents the kernel pair of `c`.

No sheaf condition on the representable presheaves of `R` and of `U` appears, the topology of
the big fppf site over `S` being subcanonical. -/
theorem isPullback_of_locallyRelated (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U R : BigFppfOver B S hS}
    (c : yoneda.obj U ⟶ F) (s t : R ⟶ U)
    (hinj : ∀ ⦃T : BigFppfOver B S hS⦄ (r r' : T ⟶ R), r ≫ t = r' ≫ t →
      r ≫ s = r' ≫ s → r = r')
    (hcomm : yoneda.map t ≫ c = yoneda.map s ≫ c)
    (hloc : ∀ ⦃T : BigFppfOver B S hS⦄ (a b : T ⟶ U), c.app (op T) a = c.app (op T) b →
      ∃ W : Sieve T, W ∈ BigFppfOver.topology B S hS T ∧
        ∀ ⦃Y : BigFppfOver B S hS⦄ (f : Y ⟶ T), W f →
          ∃ r : Y ⟶ R, r ≫ t = f ≫ a ∧ r ≫ s = f ≫ b) :
    IsPullback (yoneda.map t) (yoneda.map s) c c :=
  Stacks.Groupoids.isPullback_yoneda_of_locallyRelated _ t s c
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _)
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _) hinj hcomm hloc

end AlgebraicGeometry.Space

end
