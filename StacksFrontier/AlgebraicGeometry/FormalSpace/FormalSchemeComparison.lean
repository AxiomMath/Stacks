module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalScheme.FunctorOfPointsColimit
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Defs
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigFppfStructureSheaf

/-!
# Formal schemes à la EGA inside the fppf world

Let `S` be a scheme contained in a big fppf site `B`. A formal scheme `𝔛` à la EGA carries its
functor of points `h_𝔛(T) = Mor_{Formal Schemes}(T, 𝔛)`, which
`AlgebraicGeometry.formalSchemePoints` presents as a presheaf of `Type u` on the category of
*all* schemes. A formal algebraic space over `S`, on the other hand, is an object of
`AlgebraicGeometry.FormalSpace.FppfSheaf B S hS`, a sheaf of `Type (u + 1)` on the big fppf
site of `S`. The two descriptions differ in their site and in their value universe, so the
comparison of Stacks 0AIR cannot even be stated until `h_𝔛` is moved across both gaps. This
file does that.

The site is changed by restriction along `AlgebraicGeometry.BigFppfOver.toScheme`, the
canonical functor from the big fppf category over `S` to all schemes, which is the same device
by which the structure presheaf of the site is obtained from global functions on schemes. The
value universe is changed by `CategoryTheory.uliftFunctor`, an honest lift of the values of the
presheaf; the universe-independent predicates of
`StacksFrontier.AlgebraicGeometry.Spaces.LargeValued` are not applicable here, because they
restate the algebraic-space conditions for a presheaf that already has values in the larger
universe and so move conditions up rather than bringing a presheaf down.

Separatedness survives both moves. A covering family of the big fppf site is an fppf and hence
an fpqc covering of schemes, which is exactly
`AlgebraicGeometry.BigFppfOver.coverPreserving_toScheme`, and the functor of points is
separated for the fpqc topology by
`AlgebraicGeometry.isSeparated_fpqcTopology_formalSchemePoints`. The gluing clause is not
immediate from those two moves: it rests on the identification
`Mor(T, Spf A) = Hom_{cont}(A, Γ(T, 𝒪_T))` of Stacks 0AHZ, available in full as
`AlgebraicGeometry.bijective_spfLTRSMap`, and through it on Stacks 0AI2,
`AlgebraicGeometry.isSheaf_fpqcTopology_formalSchemePoints`. Both of those live above this file
in the import order, so the full sheaf condition is named here as a hypothesis and discharged
for an arbitrary formal scheme in
`StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSchemeComparisonSheaf`, by
`AlgebraicGeometry.FormalSpace.isFppfSheafFormalSchemePoints_formalScheme`.

## Main definitions

* `AlgebraicGeometry.FormalSpace.formalSchemeFppfPresheaf`: the functor of points of a formal
  scheme, restricted to the big fppf site of `S` and with its values lifted to `Type (u + 1)`.
* `AlgebraicGeometry.FormalSpace.formalSchemeFppfPresheafFunctor`: the same construction as a
  functor of the formal scheme.
* `AlgebraicGeometry.FormalSpace.IsFppfSheafFormalSchemePoints`: the fppf sheaf condition on
  that presheaf. It is named as a hypothesis here, this file lying below the proof in the import
  order, and is discharged for an arbitrary formal scheme by
  `AlgebraicGeometry.FormalSpace.isFppfSheafFormalSchemePoints_formalScheme`.
* `AlgebraicGeometry.FormalSpace.formalSchemeFppfSheaf`: granted that hypothesis, the functor of
  points as an object of `AlgebraicGeometry.FormalSpace.FppfSheaf B S hS`, which is the ambient
  category in which formal algebraic spaces over `S` live.
* `AlgebraicGeometry.FormalSpace.IsFormalAlgebraicSpaceFormalSchemePoints`: the conclusion of
  Stacks 0AIR for a single formal scheme, now a well-typed proposition. It is proved, for a
  formal scheme with an affine open covering and under the set-theoretic condition of
  Stacks 0AIS, in
  `StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSchemeComparisonAtlas`.

## Main results

* `AlgebraicGeometry.FormalSpace.isSeparated_formalSchemeFppfPresheaf`: the restricted and
  lifted functor of points is separated for the topology of the big fppf site of `S`.
* `AlgebraicGeometry.FormalSpace.isFppfSheafFormalSchemePoints_of_exists_isAmalgamation`: by
  that separatedness, the sheaf condition reduces to the existence of an amalgamation for every
  compatible family. That is the shape in which the clause is discharged, the amalgamations
  coming from `AlgebraicGeometry.exists_comp_eq_of_flat_surjective`.

## Implementation notes

The presheaf is written with its restriction bracketed to the left,
`(G.op ⋙ h_𝔛) ⋙ uliftFunctor`, which is the shape in which the two transport lemmas below
compose.

The two transport lemmas are stated for an arbitrary site and functor rather than for the fppf
site, because neither uses anything about schemes: `isSeparatedFor_comp_uliftFunctor` only uses
that `ULift.up` is a bijection, and `isSeparatedFor_op_comp` is the uniqueness half of
`Stacks.Sites.isSheafFor_op_comp`, which needs no compatibility hypothesis on the functor.

The sheaf condition is recorded as a `Prop`-valued definition rather than as a field of a
structure, so that a later proof of the gluing clause discharges it in one step.

## References

* [EGA I, Chapter I, Section 10]
* [Stacks Project, Tag 0AHZ](https://stacks.math.columbia.edu/tag/0AHZ)
* [Stacks Project, Tag 0AI1](https://stacks.math.columbia.edu/tag/0AI1)
* [Stacks Project, Tag 0AI2](https://stacks.math.columbia.edu/tag/0AI2)
* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0AIR](https://stacks.math.columbia.edu/tag/0AIR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w w' v₁ v₂ u₁ u₂ u

namespace AlgebraicGeometry.FormalSpace

/-! ### Transport of separatedness

Separatedness of a presheaf of types passes through a lift of its values and through
restriction along a functor whose covering sieves have covering images. -/

section Transport

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- Separatedness for a presieve is unchanged by lifting the values of a presheaf to a larger
universe: an amalgamation of a family of lifted elements is a lift of an amalgamation of the
underlying family, and `ULift.up` is a bijection. -/
@[sga "4 II 2.7" "partial"]
theorem isSeparatedFor_comp_uliftFunctor {P : Cᵒᵖ ⥤ Type w} {X : C} {R : Presieve X}
    (hP : Presieve.IsSeparatedFor P R) :
    Presieve.IsSeparatedFor (P ⋙ uliftFunctor.{w', w}) R := by
  intro x t₁ t₂ h₁ h₂
  refine ULift.ext (hP (fun _ f hf => (x f hf).down) t₁.down t₂.down ?_ ?_)
  · exact fun _ f hf => congrArg ULift.down (h₁ f hf)
  · exact fun _ f hf => congrArg ULift.down (h₂ f hf)

/-- Restricting a separated presheaf along a functor gives a presheaf separated for every sieve
whose image generates a covering sieve. This is the uniqueness half of
`Stacks.Sites.isSheafFor_op_comp`, which needs neither the full sheaf condition on the
presheaf nor any compatibility hypothesis on the functor. -/
theorem isSeparatedFor_op_comp {G : C ⥤ D} {K : GrothendieckTopology D} {P : Dᵒᵖ ⥤ Type w}
    (hP : Presieve.IsSeparated K P) {X : C} (T : Sieve X)
    (hT : T.functorPushforward G ∈ K (G.obj X)) :
    Presieve.IsSeparatedFor (G.op ⋙ P) T.arrows := by
  intro x y₁ y₂ hy₁ hy₂
  refine (hP _ hT).ext ?_
  rintro Y _ ⟨Z, g, h, hg, rfl⟩
  simpa using! congrArg _ ((hy₁ g hg).trans (hy₂ g hg).symm)

end Transport

/-! ### The functor of points on the big fppf site -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The functor of points `h_𝔛` of a formal scheme à la EGA, read on the big fppf site of `S`
and with its values lifted to `Type (u + 1)`.

Both moves are forced by the ambient category of formal algebraic spaces over `S`: the site is
the big fppf category over `S` rather than all schemes, and its sheaves take values one
universe above the schemes. -/
noncomputable def formalSchemeFppfPresheaf (X : FormalScheme.{u}) :
    (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1) :=
  ((BigFppfOver.toScheme B S hS).op ⋙ formalSchemePoints X) ⋙ uliftFunctor.{u + 1, u}

/-- The points of `𝔛` on an object `T` of the big fppf site of `S` are the morphisms of formal
schemes from the underlying scheme of `T` to `𝔛`, lifted to `Type (u + 1)`. -/
@[simp]
theorem formalSchemeFppfPresheaf_obj (X : FormalScheme.{u}) (T : BigFppfOver B S hS) :
    (formalSchemeFppfPresheaf B S hS X).obj (op T) =
      ULift.{u + 1} (schemeToFormalScheme.obj ((BigFppfOver.toScheme B S hS).obj T) ⟶ X) :=
  rfl

/-- A morphism of the big fppf site of `S` acts on points by precomposition with its underlying
morphism of schemes. -/
@[simp]
theorem formalSchemeFppfPresheaf_map (X : FormalScheme.{u}) {T T' : BigFppfOver B S hS}
    (g : T' ⟶ T)
    (f : ULift.{u + 1} (schemeToFormalScheme.obj ((BigFppfOver.toScheme B S hS).obj T) ⟶ X)) :
    (formalSchemeFppfPresheaf B S hS X).map g.op f =
      ULift.up (schemeToFormalScheme.map ((BigFppfOver.toScheme B S hS).map g) ≫ f.down) :=
  rfl

/-- The functor of points on the big fppf site of `S`, as a functor of the formal scheme. This
is the functor whose full faithfulness is the embedding asserted by Stacks 0AIR. -/
noncomputable def formalSchemeFppfPresheafFunctor :
    FormalScheme.{u} ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1) :=
  formalSchemePointsFunctor ⋙
    (Functor.whiskeringLeft _ _ _).obj (BigFppfOver.toScheme B S hS).op ⋙
      (Functor.whiskeringRight _ _ _).obj uliftFunctor.{u + 1, u}

/-- The functor of points functor evaluates to the functor of points. -/
theorem formalSchemeFppfPresheafFunctor_obj (X : FormalScheme.{u}) :
    (formalSchemeFppfPresheafFunctor B S hS).obj X = formalSchemeFppfPresheaf B S hS X :=
  rfl

/-- A morphism of formal schemes acts on points by postcomposition. -/
theorem formalSchemeFppfPresheafFunctor_map_app {X Y : FormalScheme.{u}} (f : X ⟶ Y)
    (T : BigFppfOver B S hS)
    (g : ULift.{u + 1} (schemeToFormalScheme.obj ((BigFppfOver.toScheme B S hS).obj T) ⟶ X)) :
    ((formalSchemeFppfPresheafFunctor B S hS).map f).app (op T) g = ULift.up (g.down ≫ f) :=
  rfl

/-! ### Separatedness -/

/-- The functor of points of a formal scheme, read on the big fppf site of `S`, is separated for
the topology of that site: a point of `𝔛` over an object `T` is determined by its restrictions
along any covering sieve of `T`.

A covering sieve of the big fppf site of `S` has fpqc covering image in the category of all
schemes, and the functor of points is separated for the fpqc topology there; separatedness then
survives the lift of the values. -/
theorem isSeparated_formalSchemeFppfPresheaf (X : FormalScheme.{u}) :
    Presieve.IsSeparated (BigFppfOver.topology B S hS) (formalSchemeFppfPresheaf B S hS X) :=
  fun _ R hR => isSeparatedFor_comp_uliftFunctor
    (isSeparatedFor_op_comp (isSeparated_fpqcTopology_formalSchemePoints X) R
      ((BigFppfOver.coverPreserving_toScheme B S hS).cover_preserve hR))

/-! ### The sheaf condition -/

/-- The fppf sheaf condition on the functor of points of a formal scheme, read on the big fppf
site of `S`.

This is the one clause of the comparison of Stacks 0AIR that this development cannot discharge.
Its separatedness half is `AlgebraicGeometry.FormalSpace.isSeparated_formalSchemeFppfPresheaf`;
its gluing half is the part of Stacks 0AI2 that rests on Stacks 0AHZ, of which only the
injectivity half is available, so the clause is carried as a hypothesis. -/
def IsFppfSheafFormalSchemePoints (X : FormalScheme.{u}) : Prop :=
  Presheaf.IsSheaf (BigFppfOver.topology B S hS) (formalSchemeFppfPresheaf B S hS X)

/-- The sheaf condition on the functor of points is the sheaf condition for presheaves of
types, which is the form in which a covering family is tested. -/
theorem isFppfSheafFormalSchemePoints_iff (X : FormalScheme.{u}) :
    IsFppfSheafFormalSchemePoints B S hS X ↔
      Presieve.IsSheaf (BigFppfOver.topology B S hS) (formalSchemeFppfPresheaf B S hS X) :=
  isSheaf_iff_isSheaf_of_type _ _

/-- **The sheaf condition reduces to the gluing clause.** Granted that every compatible family
of points of `𝔛` over a covering sieve of the big fppf site of `S` has an amalgamation, the
functor of points is an fppf sheaf; uniqueness of the amalgamation is
`AlgebraicGeometry.FormalSpace.isSeparated_formalSchemeFppfPresheaf`.

This is the form in which the clause is discharged: the amalgamations are supplied by
`AlgebraicGeometry.exists_comp_eq_of_flat_surjective`, which makes
`AlgebraicGeometry.FormalSpace.IsFppfSheafFormalSchemePoints` hold for an arbitrary formal
scheme. -/
theorem isFppfSheafFormalSchemePoints_of_exists_isAmalgamation (X : FormalScheme.{u})
    (hglue : ∀ (T : BigFppfOver B S hS) (R : Sieve T), R ∈ BigFppfOver.topology B S hS T →
      ∀ x : Presieve.FamilyOfElements (formalSchemeFppfPresheaf B S hS X) R.arrows,
        x.Compatible → ∃ t, x.IsAmalgamation t) :
    IsFppfSheafFormalSchemePoints B S hS X := by
  rw [isFppfSheafFormalSchemePoints_iff]
  exact fun _ R hR =>
    (isSeparated_formalSchemeFppfPresheaf B S hS X R hR).isSheafFor (hglue _ R hR)

/-- Granted the fppf sheaf condition, the functor of points of a formal scheme à la EGA is an
object of the ambient category in which formal algebraic spaces over `S` live. This is the
object the comparison of Stacks 0AIR is about. -/
noncomputable def formalSchemeFppfSheaf (X : FormalScheme.{u})
    (hX : IsFppfSheafFormalSchemePoints B S hS X) : FppfSheaf B S hS :=
  ⟨formalSchemeFppfPresheaf B S hS X, hX⟩

/-- The underlying presheaf of the fppf sheaf of points is the functor of points. -/
@[simp]
theorem formalSchemeFppfSheaf_obj (X : FormalScheme.{u})
    (hX : IsFppfSheafFormalSchemePoints B S hS X) :
    (formalSchemeFppfSheaf B S hS X hX).obj = formalSchemeFppfPresheaf B S hS X :=
  rfl

/-! ### The conclusion of Stacks 0AIR -/

/-- The conclusion of the comparison of Stacks 0AIR for a single formal scheme `𝔛`: granted the
fppf sheaf condition on its functor of points, the resulting fppf sheaf is a formal algebraic
space over `S` in the sense of Stacks 0AIM.

Before the restriction of the site and the lift of the values carried out above, this
proposition could not be formed at all: `AlgebraicGeometry.formalSchemePoints` is a presheaf of
`Type u` on all schemes, whereas
`AlgebraicGeometry.FormalSpace.IsFormalAlgebraicSpace` takes a sheaf of `Type (u + 1)` on the
big fppf site of `S`.

The proposition is not proved here. Beyond the sheaf condition it needs the atlas half of the
source's argument: the charts `h_{𝔛_i}` of an affine open covering of `𝔛` are affine formal
algebraic spaces by Stacks 0AIE, the maps `h_{𝔛_i} ⟶ h_𝔛` are representable open immersions,
and the family is jointly surjective, which is the data Stacks 0AIM consumes. -/
def IsFormalAlgebraicSpaceFormalSchemePoints (X : FormalScheme.{u}) : Prop :=
  ∀ hX : IsFppfSheafFormalSchemePoints B S hS X,
    IsFormalAlgebraicSpace B S hS (formalSchemeFppfSheaf B S hS X hX)

end AlgebraicGeometry.FormalSpace

end
