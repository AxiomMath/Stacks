module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import StacksFrontier.Algebra.Homology.KFlat
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.Resolution
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Strict replacements, and the strict functoriality of a complex of presheaves of modules

Let `A` be an abelian category with a derived category. A morphism `f : F → G` of `D(A)` is
rarely induced by a map of complexes `F ⟶ G`; the content of this file is that it always
becomes one after the *source* is replaced by a quasi-isomorphic complex, that the replacement
may be taken inside any class of complexes which resolves every complex — in particular the
K-flat complexes on a ringed site — and that the resulting map of complexes is then **strictly**
functorial wherever the complexes themselves are, with no comparison isomorphism intervening.

The shape to keep in mind is the square

```
   𝒪  ⟶  𝒥
   ↑       ↑
   𝒦  ⟶  ℱ
```

of [Stacks, Tag 099D]: `𝒪 ⟶ 𝒥` is a quasi-isomorphism (an injective resolution), `ℱ ⟶ 𝒥`
is a map of complexes, and one wants a complex `𝒦`, a quasi-isomorphism `𝒦 ⟶ ℱ` and a map of
complexes `𝒦 ⟶ 𝒪` making the square commute in the derived category, with `𝒦` K-flat. The
source obtains this "by the construction of `D(𝒪)`"; `exists_strictReplacement_of_quasiIso`
below is that construction, and `exists_isKFlat_strictReplacement` is it with `𝒦` K-flat on an
arbitrary ringed site.

## Main results

* `Stacks.StrictReplacement.exists_strictRepresentative`: every morphism
  `f : Q.obj F ⟶ Q.obj G` of the derived category is `Q.map a` for a map of complexes
  `a : K ⟶ G` out of a complex `K` carrying a quasi-isomorphism `s : K ⟶ F`, with
  `Q.map a = Q.map s ≫ f`.
* `Stacks.StrictReplacement.exists_strictRepresentative_of_resolving`: the same with `K` in any
  class of complexes which resolves every complex up to quasi-isomorphism.
* `Stacks.StrictReplacement.exists_strictReplacement_of_quasiIso`: the square above, stated with
  the derived morphism replaced by its two-map presentation `ℱ ⟶ 𝒥 ← 𝒪`.
* `Stacks.StrictReplacement.exists_isKFlat_strictReplacement`: that square on a ringed site, with
  `𝒦` K-flat. This is the K-flat strict replacement itself.
* `Stacks.StrictReplacement.sectionsRestrict_comp` and
  `Stacks.StrictReplacement.sectionsRestrict_naturality`: **strictness**. The sections of a
  complex of presheaves of modules at the objects of the site, with their restriction maps,
  compose *on the nose*, and a map of complexes of presheaves of modules commutes with those
  restrictions on the nose as well.

## Main definitions

* `Stacks.StrictReplacement.restrictScalarsComplex`: restriction of scalars on cochain
  complexes of modules along a homomorphism of (not necessarily commutative) rings.
* `Stacks.StrictReplacement.restrictScalarsComplexComp`: the comparison isomorphism for a
  composite of two such restrictions.
* `Stacks.StrictReplacement.sectionsFunctor`: evaluation of a complex of presheaves of modules at
  an object of the site.
* `Stacks.StrictReplacement.sectionsRestrict`: the restriction map between the complexes of
  sections at two objects, a map into restriction of scalars along the restriction of the
  structure presheaf of rings.
* `Stacks.StrictReplacement.toPresheafComplex`: the complex of presheaves of modules underlying
  a complex of sheaves of modules.

## Implementation notes

The strictification is Mathlib's calculus of right fractions in the derived category,
`DerivedCategory.right_fac`, which presents a morphism `f : Q.obj F ⟶ Q.obj G` as
`inv (Q.map s) ≫ Q.map g`; composing with `Q.map s` turns that presentation into the equation
`Q.map g = Q.map s ≫ f` with no inverse in it. Narrowing `K` to a resolving class costs one
further composition: a quasi-isomorphism `p : K' ⟶ K` from the class gives `p ≫ s` and
`p ≫ g`, and the equation is stable under precomposition. Nothing beyond the existence of the
derived category is used, so the statement is available for complexes of modules over a ring,
of presheaves of modules, and of sheaves of modules alike.

On a ringed site the resolving class is the K-flat complexes: the hypothesis of
`exists_strictRepresentative_of_resolving` is satisfied by
`Stacks.SheafOfModules.exists_kFlat_quasiIso` ([Stacks, Tag 06YS]), which is why the ringed-site
corollary carries that file's hypotheses on the site verbatim, with the existence of the derived
category added. For a small site the latter is automatic by
`SheafOfModules.hasDerivedCategory`; it is taken as a hypothesis here because it is what the
proof uses, and nothing more.

The ringed-site corollary is stated for a site whose objects, morphisms and rings share one
universe, which is the generality `Stacks.SheafOfModules.exists_kFlat_quasiIso` is available at
here. Its proof reads that theorem and nothing else about the site, so it generalizes exactly as
far as the K-flat resolution does, and no further.

The strictness half has nothing to do with the replacement and everything to do with the fact
that the replacement is a *single complex of presheaves of modules*: once `𝒦` is such a complex,
its sections at the objects of the site are complexes of modules over the section rings, and
the restriction maps between them compose on the nose, because the restriction maps of a
presheaf of modules do (`PresheafOfModules.map_comp`). That is the reason a functorial `K(A, I)`
can be obtained this way and cannot be obtained from a family of complexes indexed by a chosen
generating family, for which only an up-to-isomorphism comparison is available; see
`StacksFrontier/RingTheory/Cech/FunctorialCechFamilyObstruction.lean`.

`restrictScalarsComplex` repeats `CochainComplex.restrictScalars` of
`StacksFrontier/Algebra/Homology/KFlat.lean` at a not-necessarily-commutative ring, because the
section rings of a presheaf of rings are `RingCat` objects; the two agree definitionally for
commutative rings, which is `restrictScalarsComplex_eq`.

No `@[stacks]` attribute is attached. This is infrastructure for [Stacks, Tag 099D] — the step
its proof calls "the construction of `D(𝒪)`" — and not a clause of that tag's conclusion: no
part of the numbered statement of 099D is proved here.

## References

* [The Stacks Project, Tag 099D](https://stacks.math.columbia.edu/tag/099D)
* [The Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v u v₁ u₁

namespace Stacks.StrictReplacement

/-! ### Strictification of a derived morphism -/

section Abstract

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

/-- **A derived morphism becomes a map of complexes after replacing its source.** For every
morphism `f : Q.obj F ⟶ Q.obj G` of the derived category there are a complex `K`, a
quasi-isomorphism `s : K ⟶ F` and a map of complexes `a : K ⟶ G` with
`Q.map a = Q.map s ≫ f`.

This is the calculus of right fractions, rearranged so that no inverse appears: `right_fac`
writes `f = inv (Q.map s) ≫ Q.map a`, and composing with `Q.map s` on the left clears the
inverse. -/
theorem exists_strictRepresentative {F G : CochainComplex A ℤ}
    (f : DerivedCategory.Q.obj F ⟶ DerivedCategory.Q.obj G) :
    ∃ (K : CochainComplex A ℤ) (s : K ⟶ F) (a : K ⟶ G),
      QuasiIso s ∧ DerivedCategory.Q.map a = DerivedCategory.Q.map s ≫ f := by
  obtain ⟨K, s, hs, a, hf⟩ := DerivedCategory.right_fac f
  refine ⟨K, s, a, by rwa [← DerivedCategory.isIso_Q_map_iff_quasiIso], ?_⟩
  rw [hf, IsIso.hom_inv_id_assoc]

/-- **The strict representative may be taken in any resolving class.** If every complex of `A`
receives a quasi-isomorphism from a complex with the property `P`, then the complex `K` of
`exists_strictRepresentative` can be chosen with the property `P`. -/
theorem exists_strictRepresentative_of_resolving
    (P : CochainComplex A ℤ → Prop)
    (hP : ∀ L : CochainComplex A ℤ, ∃ (K : CochainComplex A ℤ) (p : K ⟶ L), P K ∧ QuasiIso p)
    {F G : CochainComplex A ℤ}
    (f : DerivedCategory.Q.obj F ⟶ DerivedCategory.Q.obj G) :
    ∃ (K : CochainComplex A ℤ) (s : K ⟶ F) (a : K ⟶ G),
      P K ∧ QuasiIso s ∧ DerivedCategory.Q.map a = DerivedCategory.Q.map s ≫ f := by
  obtain ⟨K₀, s₀, a₀, hs₀, ha₀⟩ := exists_strictRepresentative f
  obtain ⟨K, p, hPK, hp⟩ := hP K₀
  have h₀ : IsIso (DerivedCategory.Q.map s₀) := by
    rwa [DerivedCategory.isIso_Q_map_iff_quasiIso]
  have h₁ : IsIso (DerivedCategory.Q.map p) := by
    rwa [DerivedCategory.isIso_Q_map_iff_quasiIso]
  refine ⟨K, p ≫ s₀, p ≫ a₀, hPK, ?_, ?_⟩
  · rw [← DerivedCategory.isIso_Q_map_iff_quasiIso, DerivedCategory.Q.map_comp]
    infer_instance
  · rw [DerivedCategory.Q.map_comp, DerivedCategory.Q.map_comp, ha₀, Category.assoc]

/-- **The strict replacement square.** Given a map of complexes `v : F ⟶ J` and a
quasi-isomorphism `u : G ⟶ J`, there are a complex `K` in the resolving class `P`, a
quasi-isomorphism `s : K ⟶ F` and a map of complexes `a : K ⟶ G` such that the square

```
   G  ⟶  J
   ↑       ↑
   K  ⟶  F
```

commutes in the derived category.

Read with `G = 𝒪`, `J = 𝒥` an injective resolution of `𝒪` and `F = ℱ`, this is the diagram
[Stacks, Tag 099D] asks for; the map `a : K ⟶ 𝒪` is its augmentation. -/
theorem exists_strictReplacement_of_quasiIso
    (P : CochainComplex A ℤ → Prop)
    (hP : ∀ L : CochainComplex A ℤ, ∃ (K : CochainComplex A ℤ) (p : K ⟶ L), P K ∧ QuasiIso p)
    {F G J : CochainComplex A ℤ} (v : F ⟶ J) (u : G ⟶ J) (hu : QuasiIso u) :
    ∃ (K : CochainComplex A ℤ) (s : K ⟶ F) (a : K ⟶ G),
      P K ∧ QuasiIso s ∧
        DerivedCategory.Q.map (s ≫ v) = DerivedCategory.Q.map (a ≫ u) := by
  have hu' : IsIso (DerivedCategory.Q.map u) := by
    rwa [DerivedCategory.isIso_Q_map_iff_quasiIso]
  obtain ⟨K, s, a, hPK, hs, ha⟩ :=
    exists_strictRepresentative_of_resolving P hP
      (DerivedCategory.Q.map v ≫ inv (DerivedCategory.Q.map u))
  refine ⟨K, s, a, hPK, hs, ?_⟩
  rw [DerivedCategory.Q.map_comp, DerivedCategory.Q.map_comp, ha]
  simp

end Abstract

/-! ### The K-flat strict replacement on a ringed site -/

section RingedSite

variable (X : AlgebraicGeometry.RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

variable
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [HasDerivedCategory.{w}
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O))]

/-- **The K-flat strict replacement on a ringed site.** Let `(C, 𝒪)` be a ringed site, let
`v : F ⟶ J` be a map of complexes of `𝒪`-modules and let `u : G ⟶ J` be a quasi-isomorphism.
Then there are a **K-flat** complex `K` of `𝒪`-modules, a quasi-isomorphism `s : K ⟶ F` and a
map of complexes `a : K ⟶ G` with `s ≫ v` and `a ≫ u` equal in the derived category.

Taking `G` to be the structure sheaf in degree `0`, `J` an injective resolution of it and `F`
the complex to be replaced, this is the step the proof of [Stacks, Tag 099D] performs "by the
construction of `D(𝒪)`": a K-flat complex `𝒦` with an augmentation `𝒦 ⟶ 𝒪` and a
quasi-isomorphism onto the prescribed complex. The resolving class is the K-flat complexes,
which resolve every complex by [Stacks, Tag 06YS]. -/
theorem exists_isKFlat_strictReplacement
    {F G J :
      CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (v : F ⟶ J) (u : G ⟶ J) (hu : QuasiIso u) :
    ∃ (K : CochainComplex
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
      (s : K ⟶ F) (a : K ⟶ G),
      Stacks.SheafOfModules.IsKFlat X.O K ∧ QuasiIso s ∧
        DerivedCategory.Q.map (s ≫ v) = DerivedCategory.Q.map (a ≫ u) :=
  exists_strictReplacement_of_quasiIso _
    (fun L => Stacks.SheafOfModules.exists_kFlat_quasiIso X L) v u hu

end RingedSite

/-! ### Restriction of scalars on complexes, over an arbitrary ring -/

section RestrictScalars

/-- Restriction of scalars on cochain complexes along a homomorphism `φ : R₁ →+* R₂` of rings,
which need not be commutative: it applies `ModuleCat.restrictScalars φ` in each degree, so it
changes neither the underlying abelian groups nor the differentials.

This is `CochainComplex.restrictScalars` of `StacksFrontier/Algebra/Homology/KFlat.lean` with the
commutativity hypothesis dropped, which is needed because the rings of sections of a presheaf
of rings are objects of `RingCat`. The two agree for commutative rings by
`restrictScalarsComplex_eq`. -/
@[ega "III 6.3.10"]
abbrev restrictScalarsComplex {R₁ R₂ : Type u} [Ring R₁] [Ring R₂] (φ : R₁ →+* R₂) :
    CochainComplex (ModuleCat.{v} R₂) ℤ ⥤ CochainComplex (ModuleCat.{v} R₁) ℤ :=
  (ModuleCat.restrictScalars φ).mapHomologicalComplex (ComplexShape.up ℤ)

/-- Over commutative rings, `restrictScalarsComplex` is `CochainComplex.restrictScalars`. -/
theorem restrictScalarsComplex_eq {R₁ R₂ : Type u} [CommRing R₁] [CommRing R₂] (φ : R₁ →+* R₂) :
    restrictScalarsComplex φ = CochainComplex.restrictScalars φ :=
  rfl

/-- The comparison isomorphism identifying restriction of scalars along a composite
`χ = ψ ∘ φ` with the composite of the two restrictions, on cochain complexes. It is the
degreewise `ModuleCat.restrictScalarsComp'`, which is the identity on underlying abelian
groups. -/
def restrictScalarsComplexComp {R₁ R₂ R₃ : Type u} [Ring R₁] [Ring R₂] [Ring R₃]
    (φ : R₁ →+* R₂) (ψ : R₂ →+* R₃) (χ : R₁ →+* R₃) (h : χ = ψ.comp φ) :
    restrictScalarsComplex χ ≅
      restrictScalarsComplex ψ ⋙ restrictScalarsComplex φ :=
  NatIso.mapHomologicalComplex (ModuleCat.restrictScalarsComp' φ ψ χ h) (ComplexShape.up ℤ)

end RestrictScalars

/-! ### Sections of a complex of presheaves of modules, and their strict functoriality -/

section Sections

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}

/-- **The complex of sections at an object.** Evaluation at `U : Cᵒᵖ` carries a cochain complex
of presheaves of `R`-modules to a cochain complex of `R.obj U`-modules. -/
def sectionsFunctor (R : Cᵒᵖ ⥤ RingCat.{u}) (U : Cᵒᵖ) :
    CochainComplex (PresheafOfModules.{v} R) ℤ ⥤ CochainComplex (ModuleCat.{v} (R.obj U)) ℤ :=
  (PresheafOfModules.evaluation.{v} R U).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The term in degree `n` of the complex of sections at `U` is the module of sections
`(M.X n).obj U`. -/
@[simp]
theorem sectionsFunctor_obj_X (U : Cᵒᵖ) (M : CochainComplex (PresheafOfModules.{v} R) ℤ)
    (n : ℤ) : ((sectionsFunctor R U).obj M).X n = (M.X n).obj U :=
  rfl

/-- The degree-`n` component of the map of complexes of sections at `U` induced by `a` is the
component `(a.f n).app U`. -/
@[simp]
theorem sectionsFunctor_map_f (U : Cᵒᵖ)
    {M N : CochainComplex (PresheafOfModules.{v} R) ℤ} (a : M ⟶ N) (n : ℤ) :
    ((sectionsFunctor R U).map a).f n = (a.f n).app U :=
  rfl

/-- **The restriction map on complexes of sections.** For `f : U ⟶ V` in `Cᵒᵖ`, the restriction
maps of the terms of `M` assemble into a map of complexes of `R.obj U`-modules from the sections
at `U` to the sections at `V` restricted along `R.map f`.

Its commutation with the differentials is exactly the naturality of a morphism of presheaves of
modules, applied to each differential of `M`. -/
def sectionsRestrict (M : CochainComplex (PresheafOfModules.{v} R) ℤ) {U V : Cᵒᵖ} (f : U ⟶ V) :
    (sectionsFunctor R U).obj M ⟶
      (restrictScalarsComplex (R.map f).hom).obj ((sectionsFunctor R V).obj M) where
  f n := (M.X n).map f
  comm' n m _ := (M.d n m).naturality f

/-- The degree-`n` component of `sectionsRestrict M f` is the restriction map `(M.X n).map f`.
-/
@[simp]
theorem sectionsRestrict_f (M : CochainComplex (PresheafOfModules.{v} R) ℤ) {U V : Cᵒᵖ}
    (f : U ⟶ V) (n : ℤ) : (sectionsRestrict M f).f n = (M.X n).map f :=
  rfl

/-- **The restriction maps compose on the nose, degreewise.** -/
theorem sectionsRestrict_comp_f (M : CochainComplex (PresheafOfModules.{v} R) ℤ)
    {U V W : Cᵒᵖ} (f : U ⟶ V) (g : V ⟶ W) (n : ℤ) :
    (sectionsRestrict M (f ≫ g)).f n =
      (sectionsRestrict M f).f n ≫
        (ModuleCat.restrictScalars (R.map f).hom).map ((sectionsRestrict M g).f n) ≫
          (ModuleCat.restrictScalarsComp' (R.map f).hom (R.map g).hom (R.map (f ≫ g)).hom
            (congrArg RingCat.Hom.hom (R.map_comp f g))).inv.app ((M.X n).obj W) :=
  (M.X n).map_comp f g

/-- **Strictness.** The restriction maps between the complexes of sections compose *on the
nose*: the restriction along a composite `f ≫ g` is the composite of the two restrictions,
transported along the comparison isomorphism for the composite restriction of scalars. No
homotopy and no quasi-isomorphism intervenes, and the identity is an equality of maps of
complexes, not an isomorphism of objects of a derived category. -/
theorem sectionsRestrict_comp (M : CochainComplex (PresheafOfModules.{v} R) ℤ)
    {U V W : Cᵒᵖ} (f : U ⟶ V) (g : V ⟶ W) :
    sectionsRestrict M (f ≫ g) =
      sectionsRestrict M f ≫
        (restrictScalarsComplex (R.map f).hom).map (sectionsRestrict M g) ≫
          (restrictScalarsComplexComp (R.map f).hom (R.map g).hom (R.map (f ≫ g)).hom
            (congrArg RingCat.Hom.hom (R.map_comp f g))).inv.app
              ((sectionsFunctor R W).obj M) := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  simp [restrictScalarsComplexComp]

/-- **A map of complexes of presheaves of modules commutes with the restrictions on the nose.** -/
theorem sectionsRestrict_naturality {M N : CochainComplex (PresheafOfModules.{v} R) ℤ}
    (a : M ⟶ N) {U V : Cᵒᵖ} (f : U ⟶ V) :
    sectionsRestrict M f ≫ (restrictScalarsComplex (R.map f).hom).map
        ((sectionsFunctor R V).map a) =
      (sectionsFunctor R U).map a ≫ sectionsRestrict N f :=
  HomologicalComplex.hom_ext _ _ fun n => (a.f n).naturality f

end Sections

/-! ### Passing from sheaves of modules to presheaves of modules -/

section SheafSections

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u})

/-- **The complex of presheaves of modules underlying a complex of sheaves of modules.** It
applies the forgetful functor `SheafOfModules.forget R` in each degree; each term has the same
sections and restriction maps as the sheaf of modules it comes from. -/
def toPresheafComplex :
    CochainComplex (SheafOfModules.{v} R) ℤ ⥤ CochainComplex (PresheafOfModules.{v} R.obj) ℤ :=
  (SheafOfModules.forget R).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The term in degree `n` of the underlying complex of presheaves of modules is the presheaf
of modules `(M.X n).val` underlying `M.X n`. -/
@[simp]
theorem toPresheafComplex_obj_X (M : CochainComplex (SheafOfModules.{v} R) ℤ) (n : ℤ) :
    ((toPresheafComplex R).obj M).X n = (M.X n).val :=
  rfl

/-- The degree-`n` component of the underlying map of complexes of presheaves of modules is the
morphism `(a.f n).val` underlying `a.f n`. -/
@[simp]
theorem toPresheafComplex_map_f {M N : CochainComplex (SheafOfModules.{v} R) ℤ} (a : M ⟶ N)
    (n : ℤ) : ((toPresheafComplex R).map a).f n = (a.f n).val :=
  rfl

end SheafSections

end Stacks.StrictReplacement

end
