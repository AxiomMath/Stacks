module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraUnitEssentiallySmall
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSectionChartValue
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSectionGenerators

/-!
# Comparing the two spellings of the direct image of modules of Stacks 03LU

The unit of the Stacks 03D7 adjunction between inverse image and direct image of modules comes
in two spellings, because the direct image does.
`AlgebraicGeometry.Space.modulePushforward` takes the direct image of sheaves of sets and then
restricts scalars along the direct-image form `𝒪_Y ⟶ f_*𝒪_X` of the structure map, while
`Stacks.Sheaves.RingedToposModules.pushforwardModules` restricts scalars along the
inverse-image form `f⁻¹𝒪_Y ⟶ 𝒪_X` first and pushes forward after.  The two agree, by
`AlgebraicGeometry.Space.pushforwardModules_eq_modulePushforward`, but *not* definitionally:
that equality is the statement that the two forms of the structure map are adjunct.

So the chart component of the unit also comes in two spellings:
`AlgebraicGeometry.Space.modulePullbackUnitSection` is built from the transported adjunction
`AlgebraicGeometry.Space.modulePullbackAdjunction`, whose right adjoint is `modulePushforward`,
and `AlgebraicGeometry.Space.modulePullbackChartSection` from the untransported
`Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules`.  Each carries value lemmas the
other does not: the first is the value of a `AlgebraicGeometry.Space.ModuleFMap` and therefore
additive and semilinear over `AlgebraicGeometry.Space.chartDiagramPullback`
(`AlgebraicGeometry.Space.modulePullbackHomFMap_app`), the second is the one the
corepresentability computation of
`AlgebraicGeometry.Space.modulePullbackUnitIso_inv_val_app_one` produces.

This file assembles the comparison of the two spellings at the universes an algebraic space
requires, reads it on sections — it is the identity there — and so **identifies the two
sections**: each carries value lemmas the other does not, and after this they are available for
one map.

## Main results

* `AlgebraicGeometry.RingedToposHom.moduleSheafFunctor_map_pushforwardModulesIso`: **the
  comparison of the two spellings of the direct image of sheaves of modules is the identity on
  underlying sheaves of sets — at arbitrary universes**, which is what a ringed topos whose site
  does not live in the universe of its structure rings needs.  Its splitting
  `.pushforwardModulesIso_hom_app_comp` and the identification
  `.moduleSheafFunctor_map_eqToIso_pushforwardModules_eq` of its second factor are the two
  halves.
* `AlgebraicGeometry.Space.unit_modulePullbackAdjunction_app`: **the unit of the Stacks 03D7
  adjunction in its transported spelling is the untransported unit followed by that comparison.**
* `AlgebraicGeometry.Space.modulePushforwardIso_eq`: the comparison of the two direct images of
  modules of an algebraic space, unfolded.
* `AlgebraicGeometry.Space.pushforwardModulesIso_hom_app_val_app` and
  `.eqToIso_pushforwardModules_hom_app_val_app`: **each of the two factors of that comparison is
  the identity on sections**, for a morphism of algebraic spaces.
* `AlgebraicGeometry.Space.moduleSheafFunctor_map_modulePushforwardIso_hom_app` and
  `.modulePushforwardIso_hom_app_val_app`: **the comparison of the two direct images of modules
  of an algebraic space is the identity on underlying sheaves of sets, and so on sections.**  Its
  input is
  `AlgebraicGeometry.RingedToposHom.moduleSheafFunctor_map_pushforwardModulesIso_trans_eqToIso`,
  which drops the comparison out of a composite with an arbitrary transport of its target.
* `AlgebraicGeometry.Space.modulePullbackAdjunction_unit_val_app`: **the two spellings of the
  unit of the Stacks 03D7 adjunction agree on sections.**
* `AlgebraicGeometry.Space.modulePullbackUnitSection_eq_modulePullbackChartSection`: **the two
  spellings of the chart component of that unit are the same section**, so that the additivity
  and semilinearity of `AlgebraicGeometry.Space.modulePullbackUnitSection` and the unit value
  `AlgebraicGeometry.Space.modulePullbackUnitIso_inv_val_app_one` of
  `AlgebraicGeometry.Space.modulePullbackChartSection` hold of one map.
* Six `rfl`-level lemmas in `Stacks.Sheaves.RingedToposModules` reading a morphism of sheaves of
  modules, a composite, an identity, a composite of natural isomorphisms and two transports on
  sections, each stated on variables so that the `rfl` is cheap.

## Implementation notes

*The kernel budget is per declaration.*  The assembly of
`AlgebraicGeometry.RingedToposHom.moduleSheafFunctor_map_pushforwardModulesIso` from its two
factors is broken into three private steps that a reader would write as one `Eq.trans` chain.
That is not stylistic: each step forces the kernel to identify two spellings of one sheaf of sets,
each identification is affordable on its own, and the chain of them is not.  Splitting the term
across declarations gives each its own budget.

*Why the universes are redone here.*
`moduleSheafFunctor_map_pushforwardModulesIso_hom_app` of
`GradedAlgebraUnitEssentiallySmall` is the statement that the comparison of the two spellings is
the identity on underlying sheaves of sets, which is what a comparison of sections has to go
through.  It does **not** apply here: its file carries `EssentiallySmall` on the site for the
sake of the sheaves of graded algebras it is about.  Its *inputs* do apply: the abstract
`moduleSheafFunctor_map_pullbackRestrictScalarsIso_hom_app` of that file
is universe-general, being stated for an arbitrary finite-product-preserving functor, and
`AlgebraicGeometry.RingedToposHom.pushforwardModulesIso_hom_app_comp` below is the splitting it is
applied through, repeated at free universes.

*Why the comparison cannot be `rfl` on sections.*  The two modules `(pushforwardModules f).obj N`
and `(modulePushforward f).obj N` differ by a restriction of scalars along two *propositionally*
equal maps of sheaves of rings, so their scalar actions are not definitionally equal.  What is
definitional is the underlying sheaf of *sets*, which both present as the direct image
`AlgebraicGeometry.Space.smallEtaleDirectImage` of the underlying sheaf of sets of `N`, and a
section is an element of that.  So a comparison of sections has to be made through the underlying
sheaves of sets, which is what the lemmas in `Stacks.Sheaves.RingedToposModules` below are for.

*No composite is split at the concrete types.*  The reduction of a composite — `Iso.trans`, or
`≫` in a category of sheaves of modules — down to a composite of functions on sections is
affordable only where the ambient ringed topos is a variable: at
`smallEtaleRingedTopos B S hS Y` it forces the elaborator to unfold that topos to reach the
`Category` instance, and it does not finish.  So
`AlgebraicGeometry.RingedToposHom.moduleSheafFunctor_map_pushforwardModulesIso_trans_eqToIso`
splits the composite with `X`, `Y` and `f` still variables, and the concrete lemmas below only
instantiate it and apply lemmas that read a *single* morphism on a section.  For the same reason
`AlgebraicGeometry.Space.modulePushforwardIso_eq` is used through `congrArg` at an explicitly
typed binder rather than by rewriting inside an application.

*Why the transport is kept, rather than its target renamed.*  The generic splitting lemma takes
the second factor as a transport along an arbitrary equality `f_* = P` of functors.  Stating it
instead for `P = f_*`, so that the two factors meet with no transport, is not possible: with `P`
a variable the identity morphism of the underlying sheaf of sets does not have the right
codomain, and with `P` instantiated the statement is the one that cannot be assembled.

### Not proved here

**No `@[stacks]` attribute appears in this file.**  Identifying two spellings of one section is
not the content of a tag: Stacks 03LU is the adjunction, which
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePullback.lean` carries, and Stacks 089C,
whose cartesian-descent hypothesis is what needs the additivity, the semilinearity and the unit
value of the chart section on one map, asks for more than the identification below.

Nothing here raises a compiler limit or disables a linter.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Sheaf Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe w v u v' u'

namespace CategoryTheory.Adjunction

/-- The unit of an adjunction transported along an isomorphism of its right adjoint,
componentwise: the original unit followed by the isomorphism.
`CategoryTheory.Adjunction.ofNatIsoRight` is built from its hom-set bijection, and this reads
that bijection at the identity. -/
theorem unit_app_ofNatIsoRight {C : Type u} [Category.{v} C] {D : Type w} [Category.{v} D]
    {F : C ⥤ D} {G H : D ⥤ C} (adj : F ⊣ G) (iso : G ≅ H) (Z : C) :
    (adj.ofNatIsoRight iso).unit.app Z = adj.unit.app Z ≫ iso.hom.app (F.obj Z) := by
  rw [← Adjunction.homEquiv_id, Adjunction.homEquiv_ofNatIsoRight_apply,
    Adjunction.homEquiv_id]

end CategoryTheory.Adjunction

namespace Stacks.Sheaves.RingedToposModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

/-- Evaluating a composite of morphisms of sheaves of modules on a section is evaluating the two
factors in turn. -/
theorem comp_val_app_apply {M₁ M₂ M₃ : SheafOfModules.{w} R} (a : M₁ ⟶ M₂) (b : M₂ ⟶ M₃)
    (W : Cᵒᵖ) (x : M₁.val.obj W) :
    (a ≫ b).val.app W x = b.val.app W (a.val.app W x) :=
  rfl

/-- A morphism of sheaves of modules and the morphism of underlying sheaves of sets it induces
act the same way on sections. -/
theorem moduleSheafFunctor_map_hom_app {M₁ M₂ : SheafOfModules.{w} R} (a : M₁ ⟶ M₂)
    (W : Cᵒᵖ) (x : M₁.val.obj W) :
    ((Sheaf.moduleSheafFunctor R).map a).hom.app W x = a.val.app W x :=
  rfl

/-- The identity morphism of a sheaf of sets acts as the identity on sections. -/
theorem id_hom_app_apply (P : Sheaf J (Type w)) (W : Cᵒᵖ) (x : P.obj.obj W) :
    (CategoryStruct.id P).hom.app W x = x :=
  rfl

/-- A composite of two natural isomorphisms of functors into sheaves of modules, read on a
section: the two factors in turn. -/
theorem isoTrans_hom_app_val_app {A : Type u'} [Category.{v'} A]
    {F G H : A ⥤ SheafOfModules.{w} R} (α : F ≅ G) (β : G ≅ H) (N : A) (W : Cᵒᵖ)
    (x : (F.obj N).val.obj W) :
    ((α ≪≫ β).hom.app N).val.app W x
      = (β.hom.app N).val.app W ((α.hom.app N).val.app W x) :=
  rfl

/-- The transport along an equality of functors into sheaves of modules is a cast on sections.
Proved by `cases` on the equality, which is what makes it cheap: both functors are variables. -/
theorem eqToIso_hom_app_val_app {A : Type u'} [Category.{v'} A]
    {P Q : A ⥤ SheafOfModules.{w} R} (h : P = Q) (N : A) (W : Cᵒᵖ)
    (y : (P.obj N).val.obj W) :
    ((eqToIso h).hom.app N).val.app W y
      = cast (congrArg
          (fun T : A ⥤ SheafOfModules.{w} R ↦ ((T.obj N).val.obj W : Type w)) h) y := by
  cases h
  rfl

/-- The transport along an equality of sheaves of sets is a cast on sections.  Proved by `cases`
on the equality, which is what makes it cheap: both sheaves are variables. -/
theorem eqToHom_hom_app_apply {P Q : Sheaf J (Type w)} (h : P = Q) (W : Cᵒᵖ)
    (z : P.obj.obj W) :
    (eqToHom h).hom.app W z
      = cast (congrArg (fun T : Sheaf J (Type w) ↦ (T.obj.obj W : Type w)) h) z := by
  cases h
  rfl

/-- The underlying morphism of sheaves of sets of the transport along an equality of functors
into sheaves of modules is itself a transport.  Proved by `cases` on the equality, which is what
makes it cheap: both functors are variables. -/
theorem moduleSheafFunctor_map_eqToIso_hom_app {A : Type u'} [Category.{v'} A]
    {P Q : A ⥤ SheafOfModules.{w} R} (h : P = Q) (N : A) :
    (Sheaf.moduleSheafFunctor R).map ((eqToIso h).hom.app N)
      = eqToHom (congrArg
          (fun T : A ⥤ SheafOfModules.{w} R ↦
            (Sheaf.moduleSheafFunctor R).obj (T.obj N)) h) := by
  cases h
  exact CategoryTheory.Functor.map_id _ _

end Stacks.Sheaves.RingedToposModules

namespace AlgebraicGeometry.RingedToposHom

open Stacks.Sheaves.RingedToposModules Stacks.Sheaves.GradedAlgebraEssentiallySmall

variable {X Y : AlgebraicGeometry.RingedTopos}
  [X.J.HasSheafCompose (CategoryTheory.forget RingCat)]
  [Y.J.HasSheafCompose (CategoryTheory.forget RingCat)]
  [X.J.HasSheafCompose (CategoryTheory.forget₂ CommRingCat RingCat)]
  [Y.J.HasSheafCompose (CategoryTheory.forget₂ CommRingCat RingCat)]
  [X.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat)]
  [Y.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat)]
  (f : AlgebraicGeometry.RingedToposHom X Y)

/-- The comparison between the two spellings of the direct image of sheaves of modules splits
into the whiskered comparison of inverse images and the transport along the equality of
functors.  This is
`Stacks.Sheaves.GradedAlgebraEssentiallySmall.pushforwardModulesIso_hom_app_eq` at arbitrary
universes. -/
theorem pushforwardModulesIso_hom_app_comp
    (N : SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    f.pushforwardModulesIso.hom.app N
      = (CategoryTheory.Functor.isoWhiskerRight
          (pullbackRestrictScalarsIso f.toToposHom.pushforward f.ringFsharpInverseImage)
          (SheafOfModules.restrictScalars
            (ringUnit f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))).hom.app N ≫
        (eqToIso f.pushforwardModules_eq).hom.app N :=
  NatTrans.comp_app _ _ N


/-- The transport along the equality of the two direct images is the identity on underlying
sheaves of sets. -/
theorem moduleSheafFunctor_map_eqToIso_pushforwardModules_eq
    (N : SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
        ((eqToIso f.pushforwardModules_eq).hom.app N)
      = CategoryStruct.id
        (f.toToposHom.pushforward.obj
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N)) :=
  (moduleSheafFunctor_map_eqToIso_hom_app f.pushforwardModules_eq N).trans
    (eqToHom_refl _ _)

/-- The comparison, on underlying sheaves of sets, as a composite of its two factors. -/
private theorem moduleSheafFunctor_map_pushforwardModulesIso_comp
    (N : SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
        (f.pushforwardModulesIso.hom.app N)
      = (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
          ((CategoryTheory.Functor.isoWhiskerRight
            (pullbackRestrictScalarsIso f.toToposHom.pushforward f.ringFsharpInverseImage)
            (SheafOfModules.restrictScalars
              (ringUnit f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))).hom.app N) ≫
        (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
          ((eqToIso f.pushforwardModules_eq).hom.app N) :=
  (congrArg (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
      (pushforwardModulesIso_hom_app_comp f N)).trans
    ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map_comp _ _)

/-- The first factor of that composite is an identity. -/
private theorem moduleSheafFunctor_map_whiskered_comp
    (N : SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
        ((CategoryTheory.Functor.isoWhiskerRight
            (pullbackRestrictScalarsIso f.toToposHom.pushforward f.ringFsharpInverseImage)
            (SheafOfModules.restrictScalars
              (ringUnit f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))).hom.app N) ≫
        (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
          ((eqToIso f.pushforwardModules_eq).hom.app N)
      = CategoryStruct.id
          (f.toToposHom.pushforward.obj
            (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N)) ≫
        (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
          ((eqToIso f.pushforwardModules_eq).hom.app N) :=
  congrArg
    (fun p ↦ p ≫ (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
      ((eqToIso f.pushforwardModules_eq).hom.app N))
    (moduleSheafFunctor_map_pullbackRestrictScalarsIso_hom_app
      f.toToposHom.pushforward f.ringFsharpInverseImage
      (ringUnit f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) N)

/-- And so is the second. -/
private theorem id_comp_moduleSheafFunctor_map_eqToIso
    (N : SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    CategoryStruct.id
          (f.toToposHom.pushforward.obj
            (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N)) ≫
        (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
          ((eqToIso f.pushforwardModules_eq).hom.app N)
      = CategoryStruct.id
        (f.toToposHom.pushforward.obj
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N)) :=
  (Category.id_comp _).trans (moduleSheafFunctor_map_eqToIso_pushforwardModules_eq f N)

/-- **The comparison between the two spellings of the direct image of sheaves of modules is the
identity on underlying sheaves of sets.**  Neither the comparison of inverse images nor the
equality of the two restrictions of scalars changes the underlying sheaf of sets.

This is
`moduleSheafFunctor_map_pushforwardModulesIso_hom_app` of
`GradedAlgebraUnitEssentiallySmall` at arbitrary universes, which is what a ringed topos whose
site does not live in the universe of its structure rings — the small étale ringed topos of an
algebraic space, for instance — needs; see
this file's implementation notes. -/
theorem moduleSheafFunctor_map_pushforwardModulesIso
    (N : SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
        (f.pushforwardModulesIso.hom.app N)
      = CategoryStruct.id
        (f.toToposHom.pushforward.obj
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N)) :=
  ((moduleSheafFunctor_map_pushforwardModulesIso_comp f N).trans
    (moduleSheafFunctor_map_whiskered_comp f N)).trans
      (id_comp_moduleSheafFunctor_map_eqToIso f N)

/-- **The comparison drops out of a composite with a transport of its target, on underlying
sheaves of sets**: only the transport survives.  The transport is along an arbitrary equality
`f_* = P` of functors, so this reads the comparison composed with any renaming of the direct
image it lands in. -/
theorem moduleSheafFunctor_map_pushforwardModulesIso_trans_eqToIso
    {P : SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⥤
      SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)}
    (h : f.pushforwardModules = P)
    (N : SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
        ((f.pushforwardModulesIso ≪≫ eqToIso h).hom.app N)
      = CategoryStruct.id
          (f.toToposHom.pushforward.obj
            (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N)) ≫
        (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
          ((eqToIso h).hom.app N) :=
  (congrArg (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
      (NatTrans.comp_app f.pushforwardModulesIso.hom (eqToIso h).hom N)).trans
    (((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map_comp _ _).trans
      (congrArg
        (fun p ↦ p ≫ (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
          ((eqToIso h).hom.app N))
        (moduleSheafFunctor_map_pushforwardModulesIso f N)))

/-- `moduleSheafFunctor_map_pushforwardModulesIso_trans_eqToIso` for an isomorphism **given with
its factorization** through the comparison and the transport, rather than spelled as that
composite.

The two are the same statement, and the difference is what makes the instantiation affordable.
Asking unification to recognise a concrete isomorphism — `AlgebraicGeometry.Space`'s
`modulePushforwardIso`, say — as `f.pushforwardModulesIso ≪≫ eqToIso h` *inside an application to
a section* does not finish: the identification then has to be made under the implicit object
arguments of the morphism and of the coercion to a function, where the two spellings of the
direct image have to be reconciled.  Taking the isomorphism and its factorization as arguments
spends that identification once, against an equation of isomorphisms, where it is affordable. -/
theorem moduleSheafFunctor_map_hom_app_of_pushforwardModulesIso_trans_eqToIso
    {P : SheafOfModules ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
      SheafOfModules ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))}
    (h : f.pushforwardModules = P)
    (e : Stacks.Sheaves.RingedToposModules.pushforwardModules f.toRingedToposModulesHom ≅ P)
    (he : e = f.pushforwardModulesIso ≪≫ eqToIso h)
    (N : SheafOfModules ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map (e.hom.app N)
      = CategoryStruct.id
          (f.toToposHom.pushforward.obj
            (Sheaf.moduleSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) N)) ≫
        (Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map
          ((eqToIso h).hom.app N) :=
  (congrArg
      (fun t : Stacks.Sheaves.RingedToposModules.pushforwardModules
          f.toRingedToposModulesHom ≅ P ↦
        (Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map
          (t.hom.app N)) he).trans
    (moduleSheafFunctor_map_pushforwardModulesIso_trans_eqToIso f h N)

end AlgebraicGeometry.RingedToposHom

namespace AlgebraicGeometry.Space

open Stacks.Sheaves.RingedToposModules

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-! ### The unit of the transported adjunction -/

/-- **The unit of the Stacks 03D7 adjunction in its transported spelling** is the unit in the
untransported spelling followed by the comparison
`AlgebraicGeometry.Space.modulePushforwardIso` of the two direct images.  This is
`CategoryTheory.Adjunction.unit_app_ofNatIsoRight` at the transport
`AlgebraicGeometry.Space.modulePullbackAdjunction` is defined by. -/
theorem unit_modulePullbackAdjunction_app (M : Modules.{u, u} B S hS Y.1 Y.2) :
    (modulePullbackAdjunction B S hS f).unit.app M
      = (pullbackAdjPushforwardModules
            (smallEtaleRingedToposModulesHom B S hS f)).unit.app M ≫
        (modulePushforwardIso B S hS f).hom.app ((modulePullback B S hS f).obj M) := by
  rw [modulePullbackAdjunction]
  exact Adjunction.unit_app_ofNatIsoRight _ _ M

/-! ### The comparison of the two direct images, on sections -/

/-- The comparison of the two direct images of modules, unfolded: the comparison of the two
spellings for the morphism of ringed topoi, followed by the component-wise identification
`AlgebraicGeometry.Space.pushforwardModulesIsoModulePushforward` of the two restrictions of
scalars. -/
theorem modulePushforwardIso_eq :
    modulePushforwardIso B S hS f
      = (smallEtaleRingedToposHom B S hS f).pushforwardModulesIso ≪≫
        pushforwardModulesIsoModulePushforward B S hS f :=
  rfl


/-- **The comparison of inverse images is the identity on sections**, for a morphism of algebraic
spaces.  This is
`AlgebraicGeometry.RingedToposHom.moduleSheafFunctor_map_pushforwardModulesIso` read on a
section. -/
theorem pushforwardModulesIso_hom_app_val_app (N : Modules.{u, u} B S hS X.1 X.2)
    (W : (SmallEtale B S hS Y.1)ᵒᵖ)
    (y : ((modulePushforward B S hS f).obj N).val.obj W) :
    ((smallEtaleRingedToposHom B S hS f).pushforwardModulesIso.hom.app N).val.app W y = y :=
  (moduleSheafFunctor_map_hom_app
      ((smallEtaleRingedToposHom B S hS f).pushforwardModulesIso.hom.app N) W y).symm.trans
    ((congrArg (fun m ↦ m.hom.app W y)
        (AlgebraicGeometry.RingedToposHom.moduleSheafFunctor_map_pushforwardModulesIso
          (smallEtaleRingedToposHom B S hS f) N)).trans
      (id_hom_app_apply
        ((smallEtaleDirectImage B S hS f).obj (moduleSetSheaf B S hS X N)) W y))

/-- **The transport along the equality of the two direct images of modules is the identity on
sections.**  The two modules have the same underlying sheaf of sets, so the cast
`Stacks.Sheaves.RingedToposModules.eqToIso_hom_app_val_app` produces is a cast along a proof of
reflexivity. -/
theorem eqToIso_pushforwardModules_hom_app_val_app (N : Modules.{u, u} B S hS X.1 X.2)
    (W : (SmallEtale B S hS Y.1)ᵒᵖ)
    (y : ((modulePushforward B S hS f).obj N).val.obj W) :
    ((eqToIso (pushforwardModules_eq_modulePushforward B S hS f)).hom.app N).val.app W y = y :=
  (eqToIso_hom_app_val_app (pushforwardModules_eq_modulePushforward B S hS f) N W y).trans rfl

/-- **The component-wise identification of the two direct images of modules is the transport
along their equality.**  Both are isomorphisms between the same two functors and both are the
identity on sections —
`AlgebraicGeometry.Space.pushforwardModulesIsoModulePushforward_hom_app_val_app`
and `AlgebraicGeometry.Space.eqToIso_pushforwardModules_hom_app_val_app` — and a morphism of
sheaves of modules is determined by its action on sections.

The two are *not* definitionally equal: the transport is stuck on the opaque proof
`AlgebraicGeometry.Space.forgetCommRingSheaf_map_fSharp`, which is exactly why
`AlgebraicGeometry.Space.pushforwardModulesIsoModulePushforward` exists.  This records that
nothing is given up by the replacement, and it is what lets a consumer stated over the
transport —
`Stacks.Sheaves.GradedAlgebraEssentiallySmall.moduleSheafFunctor_map_ofNatIsoRight_unit_app`,
whose factorization hypothesis is spelled with `CategoryTheory.eqToIso` — still be applied to
`AlgebraicGeometry.Space.modulePushforwardIso`. -/
theorem pushforwardModulesIsoModulePushforward_eq_eqToIso :
    pushforwardModulesIsoModulePushforward B S hS f =
      eqToIso (pushforwardModules_eq_modulePushforward B S hS f) := by
  apply Iso.ext
  apply NatTrans.ext
  funext N
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.Hom.ext
  funext W
  apply ModuleCat.Hom.ext
  ext y
  exact (pushforwardModulesIsoModulePushforward_hom_app_val_app B S hS f N W y).trans
    (eqToIso_pushforwardModules_hom_app_val_app B S hS f N W y).symm

/-- `AlgebraicGeometry.Space.modulePushforwardIso_eq` with its second factor spelled as the
transport along `AlgebraicGeometry.Space.pushforwardModules_eq_modulePushforward`, which is the
shape the factorization hypothesis of
`Stacks.Sheaves.GradedAlgebraEssentiallySmall.moduleSheafFunctor_map_ofNatIsoRight_unit_app`
asks for. -/
theorem modulePushforwardIso_eq_eqToIso :
    modulePushforwardIso B S hS f
      = (smallEtaleRingedToposHom B S hS f).pushforwardModulesIso ≪≫
        eqToIso (pushforwardModules_eq_modulePushforward B S hS f) :=
  (modulePushforwardIso_eq B S hS f).trans
    (congrArg
      (fun e : (smallEtaleRingedToposHom B S hS f).pushforwardModules ≅
          modulePushforward B S hS f ↦
        (smallEtaleRingedToposHom B S hS f).pushforwardModulesIso ≪≫ e)
      (pushforwardModulesIsoModulePushforward_eq_eqToIso B S hS f))

/-- **The comparison of the two direct images of modules is the identity on sections**, for a
morphism of algebraic spaces.  Both factors are: the comparison of the two spellings for the
morphism of ringed topoi by
`AlgebraicGeometry.Space.pushforwardModulesIso_hom_app_val_app`, and the component-wise
identification of the two restrictions of scalars by
`AlgebraicGeometry.Space.pushforwardModulesIsoModulePushforward_hom_app_val_app`, whose data is
the identity.

This is what identifies the two spellings of the unit of the Stacks 03D7 adjunction. -/
theorem modulePushforwardIso_hom_app_val_app (N : Modules.{u, u} B S hS X.1 X.2)
    (W : (SmallEtale B S hS Y.1)ᵒᵖ)
    (y : ((modulePushforward B S hS f).obj N).val.obj W) :
    ((modulePushforwardIso B S hS f).hom.app N).val.app W y = y :=
  (isoTrans_hom_app_val_app (smallEtaleRingedToposHom B S hS f).pushforwardModulesIso
      (pushforwardModulesIsoModulePushforward B S hS f) N W y).trans
    ((congrArg
        (fun z ↦ ((pushforwardModulesIsoModulePushforward B S hS f).hom.app N).val.app W z)
        (pushforwardModulesIso_hom_app_val_app B S hS f N W y)).trans
      (pushforwardModulesIsoModulePushforward_hom_app_val_app B S hS f N W y))

/-- **The comparison of the two direct images of modules of an algebraic space is the identity on
underlying sheaves of sets.**  Neither the comparison of the two spellings of the direct image
nor the identification of the two restrictions of scalars changes the underlying sheaf of sets,
which both direct images present as `AlgebraicGeometry.Space.smallEtaleDirectImage`. -/
theorem moduleSheafFunctor_map_modulePushforwardIso_hom_app
    (N : Modules.{u, u} B S hS X.1 X.2) :
    (Sheaf.moduleSheafFunctor
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS Y).O)).map
        ((modulePushforwardIso B S hS f).hom.app N)
      = CategoryStruct.id ((smallEtaleDirectImage B S hS f).obj (moduleSetSheaf B S hS X N)) :=
  Sheaf.hom_ext_sections fun W y ↦
    (moduleSheafFunctor_map_hom_app ((modulePushforwardIso B S hS f).hom.app N) W y).trans
      ((modulePushforwardIso_hom_app_val_app B S hS f N W y).trans
        (id_hom_app_apply ((smallEtaleDirectImage B S hS f).obj (moduleSetSheaf B S hS X N))
          W y).symm)

/-! ### The two spellings of the unit, and of the chart section -/

/-- Evaluating a composite of morphisms of `𝒪_Y`-modules on a section is evaluating the two
factors in turn.  Stated at `AlgebraicGeometry.Space.Modules` rather than at the sheaves of
modules of a ringed topos, which is what keeps the `rfl` affordable. -/
private theorem comp_val_app_apply_modules {M₁ M₂ M₃ : Modules.{u, u} B S hS Y.1 Y.2}
    (a : M₁ ⟶ M₂) (b : M₂ ⟶ M₃) (W : (SmallEtale B S hS Y.1)ᵒᵖ) (s : M₁.val.obj W) :
    (a ≫ b).val.app W s = b.val.app W (a.val.app W s) :=
  rfl

/-- **The two spellings of the unit of the Stacks 03D7 adjunction agree on sections.**  The
transported unit of `AlgebraicGeometry.Space.modulePullbackAdjunction` and the untransported one
differ by the comparison of the two direct images, which is the identity on sections. -/
theorem modulePullbackAdjunction_unit_val_app (M : Modules.{u, u} B S hS Y.1 Y.2)
    (W : (SmallEtale B S hS Y.1)ᵒᵖ) (s : M.val.obj W) :
    ((modulePullbackAdjunction B S hS f).unit.app M).val.app W s
      = ((pullbackAdjPushforwardModules
          (smallEtaleRingedToposModulesHom B S hS f)).unit.app M).val.app W s :=
  (congrArg
    (fun m : M ⟶ (modulePushforward B S hS f).obj ((modulePullback B S hS f).obj M) ↦
      m.val.app W s)
    (unit_modulePullbackAdjunction_app B S hS f M)).trans
    ((comp_val_app_apply_modules B S hS _ _ W s).trans
      (modulePushforwardIso_hom_app_val_app B S hS f _ W _))

/-- **The two spellings of the chart component of the unit of the Stacks 03D7 adjunction are the
same section.**  Both are the chart projection of the direct image applied to a value of the
unit, and the two units agree on sections. -/
theorem modulePullbackUnitSection_eq_modulePullbackChartSection
    (M : Modules.{u, u} B S hS Y.1 Y.2) (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (s : M.val.obj (op d.V)) :
    modulePullbackUnitSection B S hS f M d s = modulePullbackChartSection B S hS f M d s :=
  congrArg
    ((moduleChartProjection B S hS f d.V (indexOfChartDiagram B S hS f d)).app
      (moduleSetSheaf B S hS X ((modulePullback B S hS f).obj M)))
    (modulePullbackAdjunction_unit_val_app B S hS f M (op d.V) s)

end AlgebraicGeometry.Space

end
