module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.RepresentableEqualizer
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SheafRepresentability.Subcanonical
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The sheaf of solutions of a standard presentation, and the representable sheaf it presents

Let `S` be a scheme of a big étale site and let `P₁, …, P_n ∈ Γ(S, ⊤)[x₁, …, x_n]`.  Every étale
chart `U` of `S` carries a structure morphism `U ⟶ S`, hence a ring map `Γ(S, ⊤) ⟶ Γ(U, ⊤)` along
which the coefficients of the `Pⱼ` may be pushed, and one may ask for the tuples
`a : Fin n → Γ(U, ⊤)` at which the pushed `Pⱼ` all vanish.  These tuples form a presheaf on the
small étale site of `S` — `Stacks.EtaleCohomology.solutionPresheaf` — because a morphism of charts
induces a ring map carrying solutions to solutions.

When `S` is affine and `V` is an affine étale chart of `S` whose ring of global functions is
*presented* by the `Pⱼ` over `Γ(S, ⊤)`, this presheaf of solutions is the representable presheaf
`h_V`: that is `Stacks.EtaleCohomology.representableIsoSolutionPresheaf`, which assembles
`Stacks.EtaleCohomology.homOverEquivSolutions` of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/RecoveringMorphisms/RepresentableEqualizer.lean`,
by its own naturality, into an isomorphism of presheaves.  In particular the presheaf of solutions
is then a *sheaf*, and `Stacks.EtaleCohomology.representableIsoSolutionSheaf` is the isomorphism
of sheaves `h_V ≅ Sol_P` in `Sheaf(S_étale, Type u)`.

This supplies the object which step (2) of the proof of [Stacks Project, Tag 04I6] names and which
the "Where the rest of Stacks 04I6 is" section of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/RecoveringMorphisms/AffineCase.lean` recorded as
absent: a *solution sheaf*, as opposed to the pointwise bijection on each chart which
`homOverEquivSolutions` provides.  The source phrases step (2) as exhibiting `h_V` as the
equalizer of `(P, 0) : (𝒪_S)^n ⇉ (𝒪_S)^n`; the sheaf of solutions is that equalizer written out,
a tuple of sections being a solution exactly when the two maps agree on it
(`Stacks.EtaleCohomology.isSolution_iff_eq_zero`).

## Main definitions

* `AlgebraicGeometry.SmallEtale.schemeStructureHom` — the structure morphism of an étale chart,
  as a morphism of schemes.  A readability abbreviation for `B.inclusion.map U.obj.hom`, the
  spelling the rest of the library uses.
* `AlgebraicGeometry.SmallEtale.homEquivOver` — morphisms of the small étale site of `S` are
  exactly the morphisms of schemes which commute with the structure morphisms.  This packages the
  existing `Stacks.EtaleCohomology.mkHom`, `Stacks.EtaleCohomology.hom_ext` and
  `AlgebraicGeometry.SmallEtale.toScheme_map_comp_hom` as a single `Equiv`.
* `Stacks.EtaleCohomology.solutionPresheaf` — the presheaf of solutions of the system `P`.
* `Stacks.EtaleCohomology.solutionSheaf` — the same, as a sheaf, for a system which presents an
  affine étale chart.
* `Stacks.EtaleCohomology.structureTypeSheaf` — the structure sheaf of the small étale site with
  its ring operations forgotten, the `𝒪_S` of the source's `(𝒪_S)^n`.
* `Stacks.EtaleCohomology.solutionCoord` and `Stacks.EtaleCohomology.representableCoord` — the
  `n` coordinates of the inclusion `h_V ⟶ (𝒪_S)^n`, given one at a time so that the product
  `(𝒪_S)^n` need not be formed.

## Main results

* `Stacks.EtaleCohomology.representableIsoSolutionPresheaf` and
  `Stacks.EtaleCohomology.representableIsoSolutionSheaf` — the representable sheaf `h_V` is the
  sheaf of solutions of a presentation of `V`.
* `Stacks.EtaleCohomology.isSolution_solutionCoord` — the `n` coordinates equalize `(P, 0)`,
  which with `Stacks.EtaleCohomology.solutionCoord` is the source's fork, in coordinates.

## What this does not do

The fork is given in coordinates only: the product `(𝒪_S)^n`, the two maps
`(P, 0) : (𝒪_S)^n ⇉ (𝒪_S)^n` as morphisms of sheaves, and the `IsLimit` of the resulting
`CategoryTheory.Limits.Fork` are **not** constructed here, so nothing here lets the
`preservesFiniteLimits` field of a morphism of topoi act on `h_V`.  See the "What is missing"
section of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/RecoveringMorphisms/AffineCase.lean` for where that
sits in the proof of Stacks 04I6.

## References

* [Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The structure morphism of an object of the small étale site of `S`, read as a morphism of
schemes to `S`.

An object of the small étale site is a scheme of `B` equipped with a morphism to `S` whose
structure morphism is étale; this is that morphism, with the full-subcategory wrapper of
`B.Scheme` removed.  It is a readability abbreviation for `B.inclusion.map U.obj.hom`, which is
how the rest of the library spells it. -/
abbrev schemeStructureHom (U : SmallEtale B S hS) :
    (SmallEtale.toScheme B S hS).obj U ⟶ S :=
  B.inclusion.map U.obj.hom

/-- **Morphisms of the small étale site of `S` are exactly the morphisms of schemes which commute
with the structure morphisms.**  The small étale site is a full subcategory of the category of
objects over `S` in `B`, so a morphism of charts is a morphism of the underlying schemes making
the triangle over `S` commute, and nothing more.

The two directions are `Stacks.EtaleCohomology.mkHom` and the action of
`AlgebraicGeometry.SmallEtale.toScheme`; that they are mutually inverse is
`Stacks.EtaleCohomology.toScheme_map_mkHom` and `Stacks.EtaleCohomology.hom_ext`, both of which
hold definitionally here. -/
def homEquivOver (U V : SmallEtale B S hS) :
    (U ⟶ V) ≃ {p : (SmallEtale.toScheme B S hS).obj U ⟶ (SmallEtale.toScheme B S hS).obj V //
      p ≫ schemeStructureHom B S hS V = schemeStructureHom B S hS U} where
  toFun f := ⟨(SmallEtale.toScheme B S hS).map f, toScheme_map_comp_hom B S hS f⟩
  invFun p := ObjectProperty.homMk (Over.homMk (ObjectProperty.homMk p.1)
    (by apply ObjectProperty.hom_ext; exact p.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- The underlying morphism of schemes of `homEquivOver B S hS U V f` is the image of `f` under
`AlgebraicGeometry.SmallEtale.toScheme`. -/
@[simp]
theorem homEquivOver_apply_coe {U V : SmallEtale B S hS} (f : U ⟶ V) :
    (homEquivOver B S hS U V f).1 = (SmallEtale.toScheme B S hS).map f :=
  rfl

/-- The ring map on global functions induced by the structure morphism of a chart factors, along
a morphism of charts, through the structure morphism of the target chart. -/
theorem appTop_schemeStructureHom_comp {U V : SmallEtale B S hS} (f : V ⟶ U) :
    ((SmallEtale.toScheme B S hS).map f).appTop.hom.comp
        (schemeStructureHom B S hS U).appTop.hom =
      (schemeStructureHom B S hS V).appTop.hom := by
  have h : ((SmallEtale.toScheme B S hS).map f ≫ schemeStructureHom B S hS U).appTop.hom =
      (schemeStructureHom B S hS V).appTop.hom :=
    congrArg (fun t : (SmallEtale.toScheme B S hS).obj V ⟶ S => t.appTop.hom)
      (toScheme_map_comp_hom B S hS f)
  rw [← h, Scheme.Hom.comp_appTop, CommRingCat.hom_comp]

end AlgebraicGeometry.SmallEtale

namespace Stacks.EtaleCohomology

open AlgebraicGeometry.SmallEtale



variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {n : ℕ}

section Presheaf

variable (P : Fin n → MvPolynomial (Fin n) Γ(S, ⊤))

/-- The solutions of the system `P` over an étale chart `U` of `S`: the tuples
`a : Fin n → Γ(U, ⊤)` at which every `Pⱼ`, with its coefficients pushed along the structure map
`Γ(S, ⊤) ⟶ Γ(U, ⊤)`, vanishes. -/
def Solutions (U : SmallEtale B S hS) : Type u :=
  {a : Fin n → Γ((SmallEtale.toScheme B S hS).obj U, ⊤) //
    MvPolynomial.IsSolution P (schemeStructureHom B S hS U).appTop.hom a}

/-- A morphism of étale charts carries solutions to solutions, coordinatewise: it induces a ring
map on global functions, the image of a solution under a ring map solves the transported system
(`MvPolynomial.isSolution_comp`), and the transported system is the one the target chart carries
because the coefficient maps are compatible
(`AlgebraicGeometry.SmallEtale.appTop_schemeStructureHom_comp`). -/
def solutionsMap {U V : SmallEtale B S hS} (f : V ⟶ U) :
    Solutions B S hS P U → Solutions B S hS P V :=
  fun a => ⟨fun i => ((SmallEtale.toScheme B S hS).map f).appTop.hom (a.1 i), by
    have h := MvPolynomial.isSolution_comp (P := P)
      (schemeStructureHom B S hS U).appTop.hom
      ((SmallEtale.toScheme B S hS).map f).appTop.hom a.2
    rwa [appTop_schemeStructureHom_comp B S hS f] at h⟩

/-- The `i`-th coordinate of the image of a solution `a` under `solutionsMap f` is the image of the
`i`-th coordinate of `a` under the ring map on global functions induced by `f`. -/
@[simp]
theorem solutionsMap_coe {U V : SmallEtale B S hS} (f : V ⟶ U)
    (a : Solutions B S hS P U) (i : Fin n) :
    (solutionsMap B S hS P f a).1 i =
      ((SmallEtale.toScheme B S hS).map f).appTop.hom (a.1 i) :=
  rfl

/-- **The presheaf of solutions of a system of polynomial equations on the small étale site.**
Its sections over an étale chart `U` of `S` are the tuples `a : Fin n → Γ(U, ⊤)` at which every
`Pⱼ`, with its coefficients pushed along the structure map `Γ(S, ⊤) ⟶ Γ(U, ⊤)`, vanishes; a
morphism of charts acts on a solution coordinatewise.

This is the equalizer of the two maps `(P, 0) : (𝒪_S)^n ⇉ (𝒪_S)^n` of step (2) of the proof of
[Stacks Project, Tag 04I6], written out: being a solution is exactly the equation between those
two maps (`Stacks.EtaleCohomology.isSolution_iff_eq_zero`).

Neither affineness nor étaleness of anything is used here; those enter only in identifying this
presheaf with a representable one. -/
@[ega "IV 18.5.2" "partial"]
def solutionPresheaf : (SmallEtale B S hS)ᵒᵖ ⥤ Type u where
  obj U := Solutions B S hS P U.unop
  map f := TypeCat.ofHom (solutionsMap B S hS P f.unop)
  map_id U := by
    apply TypeCat.homEquiv.injective
    funext a
    simp only [TypeCat.homEquiv_apply, TypeCat.ofHom_apply, types_id_apply]
    refine Subtype.ext (funext fun i => ?_)
    simp only [solutionsMap_coe, unop_id, CategoryTheory.Functor.map_id]
    rfl
  map_comp f g := by
    apply TypeCat.homEquiv.injective
    funext a
    simp only [TypeCat.homEquiv_apply, TypeCat.ofHom_apply, types_comp_apply]
    refine Subtype.ext (funext fun i => ?_)
    simp only [solutionsMap_coe, unop_comp, CategoryTheory.Functor.map_comp,
      Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]

/-- The `i`-th coordinate of the image of a solution `a` under `(solutionPresheaf P).map f` is
the image of the `i`-th coordinate of `a` under the ring map on global functions induced by `f`. -/
@[simp]
theorem solutionPresheaf_map_coe {U V : (SmallEtale B S hS)ᵒᵖ} (f : U ⟶ V)
    (a : Solutions B S hS P U.unop) (i : Fin n) :
    (((solutionPresheaf B S hS P).map f) a).1 i =
      ((SmallEtale.toScheme B S hS).map f.unop).appTop.hom (a.1 i) :=
  rfl

/-- The structure sheaf of the small étale site of `S` with its ring operations forgotten: the
sheaf of types `𝒪_S` whose `n`-fold power the equalizer of step (2) of Stacks 04I6 is taken in. -/
abbrev structureTypeSheaf : Sheaf (SmallEtale.topology B S hS) (Type u) :=
  (sheafCompose (SmallEtale.topology B S hS) (forget CommRingCat.{u})).obj
    (SmallEtale.commRingStructureSheaf B S hS)

/-- **The `i`-th coordinate of a solution, as a map of sheaves `Sol_P ⟶ 𝒪_S`.**

These `n` maps are the components of the inclusion `h_V ⟶ (𝒪_S)^n` of the equalizer presentation
of step (2) of [Stacks Project, Tag 04I6], given one coordinate at a time so that no product need
be formed.  Naturality is `Stacks.EtaleCohomology.solutionsMap_coe`: a morphism of charts acts on a
solution coordinatewise, which is exactly the assertion that each coordinate is natural. -/
def solutionCoord (i : Fin n) :
    solutionPresheaf B S hS P ⟶ (structureTypeSheaf B S hS).obj where
  app U := TypeCat.ofHom fun a => a.1 i
  naturality _ _ _ := rfl

/-- The component at `U` of `solutionCoord P i` sends a solution `a` to its `i`-th coordinate. -/
@[simp]
theorem solutionCoord_app_apply (i : Fin n) (U : (SmallEtale B S hS)ᵒᵖ)
    (a : Solutions B S hS P U.unop) :
    (solutionCoord B S hS P i).app U a = a.1 i :=
  rfl

/-- **The coordinates of a solution solve the system.**  Together with
`Stacks.EtaleCohomology.solutionCoord` this is the fork of the equalizer presentation of step (2)
of [Stacks Project, Tag 04I6], in coordinates: the `n` maps `Sol_P ⟶ 𝒪_S` equalize the two maps
`(P, 0) : (𝒪_S)^n ⇉ (𝒪_S)^n`, because at every chart and every section the tuple of coordinates is
by construction a solution. -/
theorem isSolution_solutionCoord (U : (SmallEtale B S hS)ᵒᵖ)
    (a : Solutions B S hS P U.unop) :
    MvPolynomial.IsSolution P (schemeStructureHom B S hS U.unop).appTop.hom
      (fun i => (solutionCoord B S hS P i).app U a) :=
  a.2

end Presheaf

section Representable

variable [IsAffine S] {P : Fin n → MvPolynomial (Fin n) Γ(S, ⊤)}

/-- The sections of the representable presheaf `h_V` over a chart `U`, identified with the
solutions of the presentation over `Γ(U, ⊤)`: a morphism `U ⟶ V` of the site is a morphism of
schemes over `S` (`AlgebraicGeometry.SmallEtale.homEquivOver`), and such a morphism into an affine
`V` carrying a standard presentation is a solution of that presentation
(`Stacks.EtaleCohomology.homOverEquivSolutions`). -/
def siteHomEquivSolutions (V : SmallEtale B S hS)
    [IsAffine ((SmallEtale.toScheme B S hS).obj V)]
    (pres : StandardPresentationOver ((SmallEtale.toScheme B S hS).obj V)
      (schemeStructureHom B S hS V) P)
    (U : SmallEtale B S hS) :
    (U ⟶ V) ≃ Solutions B S hS P U :=
  (homEquivOver B S hS U V).trans
    (homOverEquivSolutions ((SmallEtale.toScheme B S hS).obj U)
      ((SmallEtale.toScheme B S hS).obj V) (schemeStructureHom B S hS V)
      (schemeStructureHom B S hS U) P pres)

/-- **The representable presheaf of an affine étale chart is the presheaf of solutions of a
presentation of it.**  This is step (2) of the proof of [Stacks Project, Tag 04I6] as a statement
about presheaves on the small étale site, rather than about one chart at a time: the identification
of `Stacks.EtaleCohomology.homOverEquivSolutions` is natural in the chart, by
`Stacks.EtaleCohomology.homOverEquivSolutions_naturality`. -/
def representableIsoSolutionPresheaf (V : SmallEtale B S hS)
    [IsAffine ((SmallEtale.toScheme B S hS).obj V)]
    (pres : StandardPresentationOver ((SmallEtale.toScheme B S hS).obj V)
      (schemeStructureHom B S hS V) P) :
    ((SmallEtale.topology B S hS).yoneda.obj V).obj ≅ solutionPresheaf B S hS P :=
  NatIso.ofComponents (fun U => (siteHomEquivSolutions B S hS V pres U.unop).toIso) <| by
    intro U U' k
    apply TypeCat.homEquiv.injective
    funext g
    simp only [TypeCat.homEquiv_apply, types_comp_apply]
    refine Subtype.ext (funext fun i => ?_)
    exact homOverEquivSolutions_naturality pres ((SmallEtale.toScheme B S hS).map k.unop)
      (toScheme_map_comp_hom B S hS k.unop)
      ⟨(SmallEtale.toScheme B S hS).map g, toScheme_map_comp_hom B S hS g⟩ i

/-- The presheaf of solutions of a presentation of an affine étale chart is a sheaf, being
isomorphic to a representable presheaf on a subcanonical site. -/
theorem solutionPresheaf_isSheaf (V : SmallEtale B S hS)
    [IsAffine ((SmallEtale.toScheme B S hS).obj V)]
    (pres : StandardPresentationOver ((SmallEtale.toScheme B S hS).obj V)
      (schemeStructureHom B S hS V) P) :
    Presheaf.IsSheaf (SmallEtale.topology B S hS) (solutionPresheaf B S hS P) :=
  (Presheaf.isSheaf_of_iso_iff (representableIsoSolutionPresheaf B S hS V pres)).1
    ((SmallEtale.topology B S hS).yoneda.obj V).property

/-- **The sheaf of solutions.**  For a system `P` presenting an affine étale chart `V` of an
affine scheme `S`, the solutions of `P` form a sheaf on the small étale site of `S`, namely the
sheaf represented by `V`.

This is the object which the source's step (2) asks for: `h_V` realized as the equalizer of
`(P, 0) : (𝒪_S)^n ⇉ (𝒪_S)^n` inside `Sheaf(S_étale, Type u)`. -/
def solutionSheaf (V : SmallEtale B S hS)
    [IsAffine ((SmallEtale.toScheme B S hS).obj V)]
    (pres : StandardPresentationOver ((SmallEtale.toScheme B S hS).obj V)
      (schemeStructureHom B S hS V) P) :
    Sheaf (SmallEtale.topology B S hS) (Type u) :=
  ⟨solutionPresheaf B S hS P, solutionPresheaf_isSheaf B S hS V pres⟩

/-- The coordinates of the equalizer presentation, read on the representable sheaf itself: the
`i`-th coordinate of the solution naming a morphism of charts `U ⟶ V`.

These `n` maps `h_V ⟶ 𝒪_S` are the fork of the equalizer presentation of step (2) of
[Stacks Project, Tag 04I6], in coordinates, and `Stacks.EtaleCohomology.isSolution_solutionCoord`
is the assertion that they equalize `(P, 0)`. -/
def representableCoord (V : SmallEtale B S hS)
    [IsAffine ((SmallEtale.toScheme B S hS).obj V)]
    (pres : StandardPresentationOver ((SmallEtale.toScheme B S hS).obj V)
      (schemeStructureHom B S hS V) P)
    (i : Fin n) :
    ((SmallEtale.topology B S hS).yoneda.obj V).obj ⟶ (structureTypeSheaf B S hS).obj :=
  (representableIsoSolutionPresheaf B S hS V pres).hom ≫ solutionCoord B S hS P i

/-- **The representable sheaf of an affine étale chart is the sheaf of solutions of a presentation
of it.** -/
def representableIsoSolutionSheaf (V : SmallEtale B S hS)
    [IsAffine ((SmallEtale.toScheme B S hS).obj V)]
    (pres : StandardPresentationOver ((SmallEtale.toScheme B S hS).obj V)
      (schemeStructureHom B S hS V) P) :
    (SmallEtale.topology B S hS).yoneda.obj V ≅ solutionSheaf B S hS V pres :=
  (fullyFaithfulSheafToPresheaf (SmallEtale.topology B S hS) (Type u)).preimageIso
    (representableIsoSolutionPresheaf B S hS V pres)

end Representable

end Stacks.EtaleCohomology

end
