module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftUnit

/-!
# Coinduced sheaves of modules, and epimorphisms at an arbitrary module universe

Let `R : Sheaf J RingCat.{u}` be a sheaf of rings on a site. For a module universe `v` that is
not known to contain the size of the site, the category `SheafOfModules.{v} R` is not known to
be abelian: a quotient of a sheaf of modules is a sheafification, and sheafification raises the
universe of the sections by the size of the site. Consequently an epimorphism of
`SheafOfModules.{v} R` carries, a priori, no local information, and the two transfer statements
of `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftUnit` are left with a residual hypothesis.

This file identifies hypotheses on the *site*, rather than on the category, which discharge
those residuals: that enough **coinduced** sheaves of modules exist at module universe `v`. Two
forms are recorded, because they are not interchangeable — see the implementation notes.

## Main definitions

* `Stacks.SheafOfModules.CoinducedModule`: the data of a sheaf of modules `E` at module universe
  `v` together with a bijection `(M ⟶ E) ≃ (M(X) ⟶ A)`, natural in `M`. Equivalently, `E` is the
  value at `A` of a right adjoint of the evaluation functor at the object `X` of the site.
* `Stacks.SheafOfModules.CoinducedFibre`: the data of a functor from `SheafOfModules.{v} R` to
  abelian groups at universe `v` together with a right adjoint landing back in
  `SheafOfModules.{v} R`. This is the shape in which a point of the topos presents itself: the
  functor is the stalk and the right adjoint the pushforward along the point.

## Main results

* `Stacks.SheafOfModules.isIso_submodule_ι_of_coinduced`: **if the coinduced sheaves of modules
  exist at module universe `v`, then every epimorphic inclusion of a submodule of a sheaf of
  modules is an isomorphism.** This is the residual of
  `Stacks.SheafOfModules.isLocallySurjective_of_epi_of_isIso_submodule_ι`, so by that theorem
  every epimorphism of `SheafOfModules.{v} R` is then locally surjective
  (`Stacks.SheafOfModules.isLocallySurjective_of_epi_of_coinduced`).
* `Stacks.SheafOfModules.mem_of_app_eq_zero_of_coinduced`: the *other* residual — that the kernel
  of a cokernel projection of a submodule inclusion is no bigger than the submodule — also
  follows, and more directly: the descent property of the projection is applied to the coinduced
  object itself.
* `Stacks.SheafOfModules.isIso_submodule_ι_of_coinducedFibres` and
  `Stacks.SheafOfModules.isLocallySurjective_of_epi_of_coinducedFibres`: the same conclusions
  from a family of coinduced fibre functors which jointly detects proper submodules.
* `Stacks.SheafOfModules.cokernelIsoMapCokernelModuleULift_of_coinduced`,
  `Stacks.SheafOfModules.shortExact_map_moduleULift_of_coinduced` and
  `Stacks.SheafOfModules.shortExact_map_moduleULift_of_coinducedFibres`: consequently the
  sectionwise universe lift carries a cokernel to a cokernel and a short exact sequence to a
  short exact sequence, at an arbitrary module universe `v`, with no hypothesis on `v` itself.

## Implementation notes

Each hypothesis is stated as *data* (a structure) rather than as a `Prop` class, because the
coinduced object is genuinely data and because the proofs use the counit of the corresponding
adjunction. Only the object, the bijection and its naturality in the source are needed;
naturality in the coefficient group, and the functoriality that would make the right adjoint a
functor, are not.

*Why both forms.* For evaluation at an object of the site the detection step is free — a
submodule containing every section over every object is everything — and the hypothesis is
strong enough for *both* residuals, because the descent property can be read on sections over a
single object. A fibre functor sees sections only through its own values, so it discharges the
submodule statement, hence local surjectivity of epimorphisms, hence the short exact sequence
transfer needed for Tag 093G, but not by itself the normality statement needed for Tag 093E.
Conversely it is the fibre form, not the evaluation form, that the known cogenerators of a sheaf
category have: on a Galois site the coinduced module of continuous functions on the group
corepresents the *fibre* functor, and on the site of a topological space the skyscraper
`i_{x*}A` corepresents the *stalk* at `x`; evaluation at a single object of either site is not
corepresented by a comparably small object, since the naive candidate — the presheaf whose
sections over `Y` are the families `(X ⟶ Y) → A` — is not a sheaf. So neither form subsumes the
other and both are recorded.

*Where these hypotheses hold, and where the question stays open.* Both follow from a coseparating
set of `v`-small sheaves of modules, by the special adjoint functor theorem
(`CategoryTheory.isRightAdjoint_of_preservesLimits_of_isCoseparating`), since evaluation and the
stalk functors preserve limits — limits of sheaves of modules being computed sectionwise. What
makes them worth isolating is that a coinduced object can be produced directly, at a module
universe `v` at which the category is *not* known to be abelian and no coseparating set is in
sight: the
skyscraper of a `v`-small group has `v`-small sections whatever the size of the space, and the
invariants of the Galois coinduced module are finite powers. The hypotheses fail exactly where
the question is genuinely open: with no relation between `v` and the size of the site there is no
reason for a corepresenting sheaf at universe `v` to exist, and a pointless topos supplies no
fibre functors.

*Why this is not the refuted abstract argument.* The full subcategory of `v`-small sheaves of
modules is closed under subobjects, finite limits and finite biproducts, and that is not enough
to decide the question: the torsion-free abelian groups form a full subcategory of `AddCommGrp`
with all three closure properties in which `2 : ℤ ⟶ ℤ` is an epimorphism with cokernel `0`, so
there "epimorphism plus monomorphism implies isomorphism" fails. Both hypotheses of this file are
*false* in that subcategory, and demonstrably so: a coinduced object for the identity functor at
`A = ℤ/2` would be a torsion-free group `E` with `Hom(ℤ, E) ≅ Hom(ℤ, ℤ/2)`, that is with
`E ≅ ℤ/2`, which has torsion. So the arguments below do not apply there, which is exactly the
check that they use something the subobject constructions of `ULiftUnit.lean` cannot.

## References

* [Stacks Project, Tag 093E](https://stacks.math.columbia.edu/tag/093E)
* [Stacks Project, Tag 093G](https://stacks.math.columbia.edu/tag/093G)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.SheafOfModules

universe t v u u₁ v₁

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}

/-- **A coinduced sheaf of modules**: an object `obj` of `SheafOfModules.{v} R` corepresenting
the functor sending `M` to the `R(X)`-linear maps from the sections of `M` over `X` to `A`.

Equivalently, `obj` is the value at `A` of a right adjoint of evaluation at `X`. Only the
bijection and its naturality in the source are recorded, because that is all the theorems below
use; in particular no functoriality in `A` is required. -/
structure CoinducedModule (R : Sheaf J RingCat.{u}) (X : Cᵒᵖ)
    (A : ModuleCat.{v} (R.obj.obj X)) where
  /-- The corepresenting sheaf of modules, at module universe `v`. -/
  obj : _root_.SheafOfModules.{v} R
  /-- Morphisms into `obj` are the same data as linear maps on the sections over `X`. -/
  equiv (M : _root_.SheafOfModules.{v} R) : (M ⟶ obj) ≃ (M.val.obj X ⟶ A)
  /-- The bijection is natural in the source. -/
  equiv_comp {M N : _root_.SheafOfModules.{v} R} (u : M ⟶ N) (g : N ⟶ obj) :
    equiv M (u ≫ g) = u.val.app X ≫ equiv N g

namespace CoinducedModule

variable {R : Sheaf J RingCat.{u}} {X : Cᵒᵖ} {A : ModuleCat.{v} (R.obj.obj X)}
  (E : CoinducedModule R X A)

/-- The counit of the corepresentation: the linear map on the sections of `E.obj` over `X`
corresponding to the identity of `E.obj`. -/
def counit : E.obj.val.obj X ⟶ A := E.equiv E.obj (𝟙 E.obj)

/-- The bijection is evaluation of the counit: every morphism `g : M ⟶ E.obj` corresponds to the
composite of its component at `X` with the counit. -/
lemma equiv_eq_comp_counit (M : _root_.SheafOfModules.{v} R) (g : M ⟶ E.obj) :
    E.equiv M g = g.val.app X ≫ E.counit := by
  conv_lhs => rw [← Category.comp_id g]
  exact E.equiv_comp g (𝟙 E.obj)

/-- The zero morphism corresponds to the zero linear map. -/
lemma equiv_zero (M : _root_.SheafOfModules.{v} R) : E.equiv M 0 = 0 := by
  rw [E.equiv_eq_comp_counit]
  change (0 : M.val.obj X ⟶ E.obj.val.obj X) ≫ E.counit = 0
  exact zero_comp

/-- A morphism into a coinduced object vanishes as soon as the corresponding linear map does. -/
lemma eq_zero_of_equiv_eq_zero {M : _root_.SheafOfModules.{v} R} (g : M ⟶ E.obj)
    (h : E.equiv M g = 0) : g = 0 :=
  (E.equiv M).injective (h.trans (E.equiv_zero M).symm)

end CoinducedModule

variable {R : Sheaf J RingCat.{u}}

/-- The morphism `g : M ⟶ E` corresponding to the quotient map of the sections over `X` by the
sections of a submodule `P` kills `P`, and detects membership in `P` on sections over `X`. This is
the step shared by the two theorems about `Stacks.SheafOfModules.CoinducedModule` below. -/
private lemma exists_comp_ι_eq_zero_of_coinduced {M : _root_.SheafOfModules.{v} R}
    (P : M.Submodule) {X : Cᵒᵖ}
    (E : CoinducedModule R X (ModuleCat.of _ (M.val.obj X ⧸ P.obj X))) :
    ∃ g : M ⟶ E.obj, (∀ x : M.val.obj X, g.val.app X x = 0 → x ∈ P.obj X) ∧ P.ι ≫ g = 0 := by
  obtain ⟨g, hg⟩ := (E.equiv M).surjective (ModuleCat.ofHom (P.obj X).mkQ)
  refine ⟨g, fun x hx => ?_, E.eq_zero_of_equiv_eq_zero _ ?_⟩
  · have hmk : (E.equiv M g) x = (Submodule.Quotient.mk x : M.val.obj X ⧸ P.obj X) :=
      congrFun (congrArg (fun φ => (ModuleCat.Hom.hom φ).toFun) hg) x
    refine (Submodule.Quotient.mk_eq_zero _).1 (hmk.symm.trans ?_)
    rw [E.equiv_eq_comp_counit]
    change E.counit (g.val.app X x) = 0
    rw [hx]
    exact map_zero (E.counit).hom
  · rw [E.equiv_comp, hg]
    refine ModuleCat.hom_ext (LinearMap.ext fun y => ?_)
    exact (Submodule.Quotient.mk_eq_zero _).2 y.2

/-- **Every epimorphic inclusion of a submodule of a sheaf of modules is an isomorphism, as soon
as the coinduced sheaves of modules exist at module universe `v`.**

The proof is three lines of mathematics. Let `x` be a section of `M` over `X` and let `A` be the
quotient of the sections of `M` over `X` by those of `P`. The quotient map corresponds, under the
corepresentation, to a morphism `g : M ⟶ E` whose restriction to `P` corresponds to the zero
map, hence vanishes. As `P.ι` is an epimorphism, `g` vanishes, so the quotient map vanishes and
`x` lies in `P`. Since this holds for every section, the inclusion is an isomorphism
(`Stacks.SheafOfModules.isIso_ι_of_forall_mem`).

The conclusion, quantified over all `M` and `P`, is equivalent to the statement that every
epimorphism of `SheafOfModules.{v} R` is locally surjective: the two implications are
`Stacks.SheafOfModules.isLocallySurjective_of_epi_of_isIso_submodule_ι` and
`Stacks.SheafOfModules.isIso_submodule_ι_of_isLocallySurjective_of_epi`. -/
theorem isIso_submodule_ι_of_coinduced
    (hco : ∀ (X : Cᵒᵖ) (A : ModuleCat.{v} (R.obj.obj X)), CoinducedModule R X A)
    (M : _root_.SheafOfModules.{v} R) (P : M.Submodule) (hP : Epi P.ι) : IsIso P.ι := by
  refine isIso_ι_of_forall_mem P fun X x => ?_
  obtain ⟨g, hmem, hg⟩ := exists_comp_ι_eq_zero_of_coinduced P (hco X (ModuleCat.of _ _))
  have hgzero : g = 0 := hP.left_cancellation g 0 (hg.trans (comp_zero (f := P.ι)).symm)
  exact hmem x (by rw [hgzero]; rfl)

/-- **Epimorphisms of `SheafOfModules.{v} R` are locally surjective, as soon as the coinduced
sheaves of modules exist at module universe `v`** — with no `HasSheafify`, no
`J.WEqualsLocallyBijective`, no `Abelian` and no `Balanced`. -/
theorem isLocallySurjective_of_epi_of_coinduced
    (hco : ∀ (X : Cᵒᵖ) (A : ModuleCat.{v} (R.obj.obj X)), CoinducedModule R X A)
    {M N : _root_.SheafOfModules.{v} R} (f : M ⟶ N) (hf : Epi f) :
    Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf R.obj).map f.val) :=
  @isLocallySurjective_of_epi_of_isIso_submodule_ι _ _ _ _
    (fun M' P hP => isIso_submodule_ι_of_coinduced hco M' P hP) _ _ f hf

/-- **The kernel of a cokernel projection of a submodule inclusion is no bigger than the
submodule, as soon as the coinduced sheaves of modules exist at module universe `v`.** This is
the residual hypothesis `hsub` of
`Stacks.SheafOfModules.mem_localClosure_of_descends_of_submodule`.

Here the descent property is used directly, and no epimorphism argument is needed: the morphism
`g : G ⟶ E` built from the quotient map kills `P`, hence factors as `π ≫ σ`, hence annihilates
every section annihilated by `π`. -/
theorem mem_of_app_eq_zero_of_coinduced
    (hco : ∀ (X : Cᵒᵖ) (A : ModuleCat.{v} (R.obj.obj X)), CoinducedModule R X A)
    (G Q : _root_.SheafOfModules.{v} R) (P : G.Submodule) (π : G ⟶ Q)
    (hdesc : ∀ (Z : _root_.SheafOfModules.{v} R) (h : G ⟶ Z), P.ι ≫ h = 0 →
      ∃ σ : Q ⟶ Z, π ≫ σ = h)
    (X : Cᵒᵖ) (x : G.val.obj X) (hx : π.val.app X x = 0) : x ∈ P.obj X := by
  obtain ⟨g, hmem, hg⟩ := exists_comp_ι_eq_zero_of_coinduced P (hco X (ModuleCat.of _ _))
  obtain ⟨σ, hσ⟩ := hdesc _ g hg
  refine hmem x ?_
  rw [← hσ]
  change σ.val.app X (π.val.app X x) = 0
  rw [hx]
  exact map_zero (σ.val.app X).hom

/-- The residual hypothesis of the cokernel transfer, discharged: every section of `G` killed by
the cokernel projection of `f` lies in the local closure of the range of `f`. -/
theorem mem_localClosure_cokernel_π_of_coinduced
    (hco : ∀ (X : Cᵒᵖ) (A : ModuleCat.{v} (R.obj.obj X)), CoinducedModule R X A)
    {F G : _root_.SheafOfModules.{v} R} (f : F ⟶ G) [HasCokernel f] (X : Cᵒᵖ)
    (x : G.val.obj X) (hx : (cokernel.π f).val.app X x = 0) :
    x ∈ (localClosure G (presheafRangeSubmodule f.val)).obj X :=
  mem_localClosure_cokernel_π_of_submodule
    (fun G' Q' P π _ _ hd => mem_of_app_eq_zero_of_coinduced hco G' Q' P π hd) f X x hx

/-! ### Coinduction along a fibre functor

The corepresentability of evaluation at an object of the site is clean, but it is not the form in
which the cogenerators of a sheaf category are usually available: on a Galois site the
corepresenting object is the module of continuous functions on the group, which corepresents the
*fibre* functor and not evaluation at any single orbit, and on the site of a topological space
the skyscraper `i_{x*}A` corepresents the stalk at `x`. Both are coinduction along a functor to
abelian groups together with a right adjoint, and a family of such functors which jointly
detects proper submodules does the same work as the family of evaluations.
-/

/-- **Coinduction along a fibre functor**: a functor from sheaves of modules at module universe
`v` to abelian groups at universe `v`, together with a right adjoint landing back in
`SheafOfModules.{v} R`.

This is the shape in which the cogenerators of a sheaf category are available when they come from
a point of the topos: `fibre` is the stalk and `coind` the pushforward along the point, and the
requirement that `coind A` be a sheaf of modules *at module universe `v`* is the statement that
the point has `v`-small fibres. -/
structure CoinducedFibre (R : Sheaf J RingCat.{u}) where
  /-- The fibre functor. -/
  fibre : _root_.SheafOfModules.{v} R ⥤ AddCommGrpCat.{v}
  /-- The fibre functor is additive; only vanishing on zero morphisms is used. -/
  fibre_map_zero {M N : _root_.SheafOfModules.{v} R} : fibre.map (0 : M ⟶ N) = 0
  /-- The sheaf of modules coinduced from an abelian group, at module universe `v`. -/
  coind : AddCommGrpCat.{v} → _root_.SheafOfModules.{v} R
  /-- Morphisms into `coind A` are the same data as homomorphisms out of the fibre. -/
  equiv (M : _root_.SheafOfModules.{v} R) (A : AddCommGrpCat.{v}) :
    (M ⟶ coind A) ≃ (fibre.obj M ⟶ A)
  /-- The bijection is natural in the source. -/
  equiv_comp {M N : _root_.SheafOfModules.{v} R} (A : AddCommGrpCat.{v}) (u : M ⟶ N)
    (g : N ⟶ coind A) : equiv M A (u ≫ g) = fibre.map u ≫ equiv N A g

namespace CoinducedFibre

variable {R : Sheaf J RingCat.{u}} (F : CoinducedFibre.{v} R)

/-- The counit of the coinduction: the homomorphism out of the fibre of `coind A` corresponding
to the identity. -/
def counit (A : AddCommGrpCat.{v}) : F.fibre.obj (F.coind A) ⟶ A :=
  F.equiv (F.coind A) A (𝟙 _)

/-- The bijection is evaluation of the counit. -/
lemma equiv_eq_comp_counit (A : AddCommGrpCat.{v}) (M : _root_.SheafOfModules.{v} R)
    (g : M ⟶ F.coind A) : F.equiv M A g = F.fibre.map g ≫ F.counit A := by
  conv_lhs => rw [← Category.comp_id g]
  exact F.equiv_comp A g (𝟙 _)

/-- The zero morphism corresponds to the zero homomorphism. -/
lemma equiv_zero (A : AddCommGrpCat.{v}) (M : _root_.SheafOfModules.{v} R) :
    F.equiv M A 0 = 0 := by
  rw [F.equiv_eq_comp_counit, F.fibre_map_zero, zero_comp]

/-- A morphism into a coinduced object vanishes as soon as the corresponding homomorphism does. -/
lemma eq_zero_of_equiv_eq_zero {A : AddCommGrpCat.{v}} {M : _root_.SheafOfModules.{v} R}
    (g : M ⟶ F.coind A) (h : F.equiv M A g = 0) : g = 0 :=
  (F.equiv M A).injective (h.trans (F.equiv_zero A M).symm)

/-- **The fibre of an epimorphic submodule inclusion is surjective.** This is the whole use of the
coinduction: the quotient of the fibre of `M` by the image of the fibre of `P` is an abelian group
at universe `v`, so the coinduced sheaf of modules exists, and the quotient map corresponds to a
morphism out of `M` which `P` kills and which therefore vanishes. -/
theorem surjective_fibre_map_ι {M : _root_.SheafOfModules.{v} R} (P : M.Submodule)
    (hP : Epi P.ι) : Function.Surjective (F.fibre.map P.ι) := by
  set φ := F.fibre.map P.ι with hφ
  set H := φ.hom.range with hH
  set A : AddCommGrpCat.{v} := AddCommGrpCat.of (F.fibre.obj M ⧸ H) with hA
  set ψ : F.fibre.obj M ⟶ A := AddCommGrpCat.ofHom (QuotientAddGroup.mk' H) with hψ
  have hφψ : φ ≫ ψ = 0 := by
    refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun y => ?_)
    exact (QuotientAddGroup.eq_zero_iff _).2 ⟨y, rfl⟩
  obtain ⟨g, hg⟩ := (F.equiv M A).surjective ψ
  have hPg : P.ι ≫ g = 0 := by
    refine F.eq_zero_of_equiv_eq_zero _ ?_
    rw [F.equiv_comp, hg, ← hφ, hφψ]
  have hgzero : g = 0 :=
    hP.left_cancellation g 0 (hPg.trans (comp_zero (f := P.ι)).symm)
  have hψzero : ψ = 0 := by rw [← hg, hgzero, F.equiv_zero]
  intro z
  refine (AddMonoidHom.mem_range (f := φ.hom)).1 ((QuotientAddGroup.eq_zero_iff z).1 ?_)
  exact congrFun (congrArg (fun χ => (AddCommGrpCat.Hom.hom χ).toFun) hψzero) z

end CoinducedFibre

/-- **Every epimorphic inclusion of a submodule of a sheaf of modules is an isomorphism, as soon
as a family of coinduced fibre functors detects proper submodules.**

The detection hypothesis is exactly joint conservativity of the family on submodule inclusions,
and it is automatic for the family of evaluations at the objects of the site; what the family buys
is that its coinduced objects live at module universe `v`. On the site of a topological space the
family is indexed by the points, with `fibre` the stalk and `coind` the skyscraper; on a Galois
site a single fibre functor suffices. -/
theorem isIso_submodule_ι_of_coinducedFibres {K : Type*} (F : K → CoinducedFibre.{v} R)
    (hdetect : ∀ (M : _root_.SheafOfModules.{v} R) (P : M.Submodule),
      (∀ a, Function.Surjective ((F a).fibre.map P.ι)) →
        ∀ (X : Cᵒᵖ) (x : M.val.obj X), x ∈ P.obj X)
    (M : _root_.SheafOfModules.{v} R) (P : M.Submodule) (hP : Epi P.ι) : IsIso P.ι :=
  isIso_ι_of_forall_mem P (hdetect M P fun a => (F a).surjective_fibre_map_ι P hP)

/-- **Epimorphisms of `SheafOfModules.{v} R` are locally surjective, as soon as a family of
coinduced fibre functors detects proper submodules.** -/
theorem isLocallySurjective_of_epi_of_coinducedFibres {K : Type*} (F : K → CoinducedFibre.{v} R)
    (hdetect : ∀ (M : _root_.SheafOfModules.{v} R) (P : M.Submodule),
      (∀ a, Function.Surjective ((F a).fibre.map P.ι)) →
        ∀ (X : Cᵒᵖ) (x : M.val.obj X), x ∈ P.obj X)
    {M N : _root_.SheafOfModules.{v} R} (f : M ⟶ N) (hf : Epi f) :
    Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf R.obj).map f.val) :=
  @isLocallySurjective_of_epi_of_isIso_submodule_ι _ _ _ _
    (fun M' P hP => isIso_submodule_ι_of_coinducedFibres F hdetect M' P hP) _ _ f hf

section CokernelTransfer

variable [HasSheafify J AddCommGrpCat.{max v t}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max v t}]

/-- **The sectionwise universe lift carries a cokernel to a cokernel**, at an arbitrary module
universe `v`, as soon as the coinduced sheaves of modules exist at `v`. This is what the finite
presentation predicate of Tag 093C needs in order to pass to cokernels, and hence what Tag 093E
needs at a free module universe. -/
def cokernelIsoMapCokernelModuleULift_of_coinduced
    (hco : ∀ (X : Cᵒᵖ) (A : ModuleCat.{v} (R.obj.obj X)), CoinducedModule R X A)
    {F G : _root_.SheafOfModules.{v} R} (f : F ⟶ G) [HasCokernel f] :
    cokernel ((moduleULift.{t, v} R).map f) ≅ (moduleULift.{t, v} R).obj (cokernel f) :=
  cokernelIsoMapCokernelModuleULift f (mem_localClosure_cokernel_π_of_coinduced hco f)

/-- **The sectionwise universe lift carries a short exact sequence to a short exact sequence**,
at an arbitrary module universe `v`, as soon as the coinduced sheaves of modules exist at `v`.
This is what Tag 093G needs at a free module universe. -/
theorem shortExact_map_moduleULift_of_coinduced
    (hco : ∀ (X : Cᵒᵖ) (A : ModuleCat.{v} (R.obj.obj X)), CoinducedModule R X A)
    (E : ShortComplex (_root_.SheafOfModules.{v} R)) (hE : E.ShortExact) :
    (E.map (moduleULift.{t, v} R)).ShortExact :=
  shortExact_map_moduleULift_of_epi_isLocallySurjective
    (fun ψ hψ => isLocallySurjective_of_epi_of_coinduced hco ψ hψ) E hE

/-- **The sectionwise universe lift carries a short exact sequence to a short exact sequence**,
at an arbitrary module universe `v`, as soon as a family of coinduced fibre functors detects
proper submodules. This is the form of the hypothesis that a point of the topos supplies, and it
is enough for Tag 093G; it is *not* enough for Tag 093E, whose residual is the normality
statement discharged by `Stacks.SheafOfModules.mem_of_app_eq_zero_of_coinduced`, where the
descent property has to be applied to the coinduced object and therefore has to be read on
sections over a single object of the site. -/
theorem shortExact_map_moduleULift_of_coinducedFibres {K : Type*} (F : K → CoinducedFibre.{v} R)
    (hdetect : ∀ (M : _root_.SheafOfModules.{v} R) (P : M.Submodule),
      (∀ a, Function.Surjective ((F a).fibre.map P.ι)) →
        ∀ (X : Cᵒᵖ) (x : M.val.obj X), x ∈ P.obj X)
    (E : ShortComplex (_root_.SheafOfModules.{v} R)) (hE : E.ShortExact) :
    (E.map (moduleULift.{t, v} R)).ShortExact :=
  shortExact_map_moduleULift_of_epi_isLocallySurjective
    (fun ψ hψ => isLocallySurjective_of_epi_of_coinducedFibres F hdetect ψ hψ) E hE

end CokernelTransfer

end Stacks.SheafOfModules

end

