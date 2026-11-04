module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedForgetColimits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UngradedAlgebras
public import StacksCore.Tactic.StacksAttribute

/-!
# The free graded module on a sheaf of graded sets

Let `R` be a sheaf of rings on a site and let `A` be a sheaf of `ℤ`-graded `R`-algebras. A
*sheaf of graded sets* is a sheaf of sets `S` together with a morphism `deg : S ⟶ underline ℤ`
to the constant sheaf of integers. The *free graded `A`-module* `A[S]` on `S` has, in total
degree `n`, the sheafification of the presheaf

`U ↦ ⨁_{s ∈ S(U), deg s = i} s · A^{n - i}(U)`

and it is characterized by having one homogeneous generator of degree `n` for every local
section of `S` of degree `n`.

This file builds that presentation, its sheafification, the graded `A`-module structure on the
result, the canonical generators, and the universal property: a family of homogeneous
generators in an arbitrary graded `A`-module extends uniquely to a homomorphism out of `A[S]`.

## Main definitions

* `Stacks.SheafOfGradedSets` is a sheaf of graded sets on a site, and
  `Stacks.SheafOfGradedSets.HasDegree S U s n` says that the local section `s` has degree `n`,
  i.e. that its degree is the image of the constant integer `n` in the constant sheaf.
* `Stacks.SheafOfGradedSets.Index S U` is the index set of the presentation: pairs of an
  integer `i` and a local section of degree `i`.
* `SheafOfModules.coeffSections S X n U` is the degreewise direct sum
  `⨁_{s} s · X^{n - deg s}(U)` for an arbitrary family of coefficients
  `X : ℤ → SheafOfModules R`, `SheafOfModules.coeffOf` its inclusion of one summand,
  `SheafOfModules.coeffPres S X n` the presheaf of modules these assemble into,
  `SheafOfModules.coeffPiece S X n` its sheafification and `SheafOfModules.coeffUnit S X n`
  the canonical morphism to it.
* `SheafOfModules.freeSections A S n U` is the degreewise direct sum
  `⨁_{s} s · A^{n - deg s}(U)`, `SheafOfModules.freeOf` is its inclusion of one summand, and
  `SheafOfModules.freePres A S n` is the presheaf of modules these assemble into.
* `SheafOfModules.freePiece A S n` is the sheafification of `freePres A S n`, and
  `SheafOfModules.freeUnit A S n` the canonical morphism to it.
* `SheafOfModules.presAct` and `SheafOfModules.freeActBilin` are the action of a homogeneous
  section of `A` on the presentation and on its sheafification.
* `SheafOfModules.freeGradedModule A S` is the free graded `A`-module `A[S]`, and
  `SheafOfModules.freeGenerator` its family of canonical generators.
* `SheafOfModules.GradedGeneratorFamily S M` is a restriction-compatible family of homogeneous
  sections of a graded module indexed by a sheaf of graded sets.
* `SheafOfModules.liftHom` is the homomorphism out of `A[S]` determined by such a family.
* `SheafOfModules.FreeGradedModuleData` packages a free graded module with its presentation,
  its generators, its universal property and its closed-generator differential, and
  `SheafOfModules.freeGradedModuleData` is the one built here.
* `SheafOfModules.dPres` is the differential of the presentation when `A` carries a
  differential: the generators are closed, so the Leibniz rule forces
  `d (s · a) = (-1)^{deg s} s · d a`, and `SheafOfModules.dPresHom` is it as a morphism of
  presheaves of modules.
* `SheafOfModules.freeD` is the differential of `A[S]`, the unique extension of `dPres` to the
  sheafification, `SheafOfModules.freeComplex` the resulting cochain complex and
  `SheafOfModules.freeDGModule` the free differential graded `D`-module `D[S]`.
* `SheafOfModules.postcompBilin` post-composes a bilinear map of presheaves of modules with a
  morphism out of its target, and `SheafOfModules.GradedModule.app_castHom`,
  `SheafOfModules.GradedModule.smul_sectionRestrict`,
  `SheafOfModules.GradedAlgebra.mul_castHom_left` are the transport lemmas the degree
  bookkeeping needs.

## Main results

* `SheafOfModules.freeActBilin_one` and `SheafOfModules.freeActBilin_assoc` are the unit and
  associativity laws of the action, so that `freeGradedModule A S` is a graded `A`-module.
* `SheafOfModules.freeGeneratorSection_eq` and `SheafOfModules.freeUnit_freeOf` identify the
  generators inside the presentation and show that every summand `s · a` of the presentation is
  the generator of `s` acted on by `a`.
* `SheafOfModules.freeActBilin_generator` computes the action of `A` on a generator.
* `SheafOfModules.liftHom_generator` and `SheafOfModules.freeGradedModule_hom_ext` are the two
  halves of the universal property: a homomorphism out of `A[S]` can be prescribed arbitrarily
  on the generators, and is determined by its values there.
* `SheafOfModules.dPres_dPres` says the differential of the presentation is square-zero, and
  `SheafOfModules.dPres_presAct` is its Leibniz rule.
* `SheafOfModules.freeD_freeD` and `SheafOfModules.freeD_freeActBilin` are the square-zero law
  and the Leibniz rule of the differential of `A[S]`, and
  `SheafOfModules.freeD_freeGeneratorSection` says every canonical generator is closed, which
  is what pins the differential down.
* `SheafOfModules.forgetToGradedModule_freeDGModule` says the graded module underlying `D[S]`
  **is** `A[S]`, where `A` is the graded algebra underlying `D` — the pieces and the action
  agree on the nose, not merely up to isomorphism. Its two halves are
  `SheafOfModules.freeDGModule_piece` and `SheafOfModules.freeDGModule_mul_app`.
* `SheafOfModules.freePiece_hom_ext`: a morphism out of a piece of `A[S]` into a sheaf of
  modules is determined by its restriction to the presentation.
* `SheafOfModules.freeGradedModuleData` is the tagged statement: it *exhibits* the free
  graded `A`-module on `S`, with everything that characterizes it, rather than asserting
  that one exists.

## Implementation notes

The base is an arbitrary sheaf of rings `R` on an arbitrary site rather than the structure
sheaf of a ringed site, and the universes of the site, the ring, the pieces of the algebra and
the values of the sheaf of graded sets are independent. The module universe of `A[S]` is
**forced**, not chosen: the sections of the presentation are a direct sum indexed by a type in
`Type w` with summands in `Type a`, so they live in `Type (max w a)` and nowhere smaller. No
universe is specialized anywhere below.

The action of `A` on the sheafification is obtained from the action on the presentation by
`Stacks.BilinearMap.extend`: a bilinear map into a *sheaf* extends uniquely along a locally
bijective morphism, and `PresheafOfModules.toSheafify` is locally bijective. This is why the
file needs `HasWeakSheafify J AddCommGrpCat` and `J.WEqualsLocallyBijective AddCommGrpCat` at
the module universe, and nothing more: no abelian structure on `SheafOfModules R`, and no
colimits of sheaves of modules. These are exactly the hypotheses under which
`PresheafOfModules.sheafification` exists. Sheafifying the action one variable at a time, rather
than through a tensor product, also keeps the three module universes independent.

Every law of the graded module whose two sides live in propositionally but not definitionally
equal degrees is stated with `HEq`, and proved by transporting along `SheafOfModules.castHom` —
for the presentation, along the companion `SheafOfModules.freeCast`. The two are related by
`SheafOfModules.castHom_freeUnit`.

The presentation is built once, for an arbitrary family of coefficients
`X : ℤ → SheafOfModules R`, and `freeSections`, `freePres` and `freePiece` are that construction
at `X = A.piece`: nothing but the degreewise pieces of `A` enters the presentation, so the
generality is free, and it is the form in which a graded `A`-module `N` appears as the
coefficients of `N[S]`. `coeffSections` and `coeffOf` are `abbrev`s, so the two layers unfold
into one another and the free module's lemmas are the general ones applied at `A.piece`. No
action is constructed at the general level: a graded sheaf of modules carries none, and the
action of `A` on `A[S]` is the content of the rest of this file.

Two shapes of the same type recur and must be kept apart in *statements*: the sections of the
presentation are `freeSections A S n U` when written as a direct sum and
`↑((freePres A S n).obj U)` when written as sections of a presheaf of modules. They are
definitionally equal, so term-mode proofs never notice, but `rw` does: a goal mixing the two is
not type-correct at `implicit` transparency and `kabstract` refuses it. Accordingly the lemmas
that are rewritten with at the level of the presentation use the direct-sum spelling, the ones
rewritten with after sheafification use the presheaf spelling, and the proofs that cross the
boundary are written as `calc` chains of `Eq.trans` and `congrArg`. For the same reason
restriction maps appear as `Stacks.sectionRestrict`, whose target type is written plainly,
rather than as `PresheafOfModules.map`, whose target is a restriction of scalars.

The differential is built in two stages. On the presentation, `dPres` is square-zero,
`R`-linear, compatible with restriction and satisfies the Leibniz rule; the signs come from
`Int.negOnePow_add` over `j + (n - j) = n`, which is exactly the statement that the sign of a
generator and the sign of its coefficient multiply to the sign of the total degree. On the
sheafification, `freeD` is obtained from `dPres` through `PresheafOfModules.sheafifyHomEquiv'`
rather than by sheafifying a morphism functorially, so that `freeD_unit` — the identity
`freeD (freeUnit ζ) = freeUnit (dPres ζ)` — is available as the one computation rule; both the
square-zero law and the Leibniz rule are then transported across it, the former by
`freePiece_hom_ext` and the latter by `Stacks.eq_of_forall_lift` on local lifts, in the same
pattern as `freeActBilin_one` and `freeActBilin_assoc`.

The differential graded module is stated for `A = D.toGradedAlgebra` rather than for a graded
algebra `A` together with a proof `D.toGradedAlgebra = A`: the type
`DifferentialGradedModule D` does not mention `A` at all, so nothing is lost, and a consumer
holding such a proof obtains the general form by `subst`.

`FreeGradedModuleData` is a bundle because that is the shape of the source's statement: the free
graded module is characterized by the conjunction of all of these properties, and no proper subset
of them is the content of Tag 0FSF. Its individual fields are the named results above. The two
spellings of the presentation's sections — `freeSections A S n U` as a direct sum and
`(presentation n).obj U` as sections of a presheaf of modules — are related in the bundle by
`presentation_obj`, which for the free module built here is the identity `LinearEquiv.refl`;
likewise `piece_iso` is `Iso.refl`. Those two fields are therefore not slack in the statement: they
are what lets a *different* construction of the free module satisfy it.

## References

* [Stacks Project, Tag 0FSF](https://stacks.math.columbia.edu/tag/0FSF)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
* [Stacks Project, Tag 0FQZ](https://stacks.math.columbia.edu/tag/0FQZ)
-/
@[expose] public section

open CategoryTheory CategoryTheory.Limits DirectSum

universe w t a v u w₁ w₂ w₃

namespace Stacks

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- A sheaf of graded sets on a site: a sheaf of sets together with a degree morphism to the
constant sheaf of integers. -/
@[stacks 0FSF "sheaf_of_graded_sets"]
structure SheafOfGradedSets (J : GrothendieckTopology C) [HasWeakSheafify J (Type w)] where
  /-- The underlying sheaf of sets. -/
  sheaf : Sheaf J (Type w)
  /-- The morphism assigning an integer degree to every local section. -/
  degree : sheaf ⟶ (constantSheaf J (Type w)).obj (ULift.{w} ℤ)

namespace SheafOfGradedSets

variable [HasWeakSheafify J (Type w)] (S : SheafOfGradedSets.{w} J)

/-- A local section has degree `n` when its degree is the image of the constant integer `n`. -/
abbrev HasDegree (U : Cᵒᵖ) (s : S.sheaf.obj.obj U) (n : ℤ) : Prop :=
  S.degree.hom.app U s =
    (toSheafify J ((Functor.const Cᵒᵖ).obj (ULift.{w} ℤ))).app U ⟨n⟩

/-- Having a given degree is preserved by restriction. -/
theorem hasDegree_map {U V : Cᵒᵖ} (f : U ⟶ V) {s : S.sheaf.obj.obj U} {n : ℤ}
    (hs : S.HasDegree U s n) : S.HasDegree V (S.sheaf.obj.map f s) n := by
  have h2 := NatTrans.naturality_apply
    (toSheafify J ((Functor.const Cᵒᵖ).obj (ULift.{w} ℤ))) f (ULift.up (α := ℤ) n)
  refine Eq.trans (NatTrans.naturality_apply S.degree.hom f s) ?_
  rw [hs]
  exact h2.symm

/-- The index set of the free graded module: pairs of an integer and a local section of that
degree. -/
abbrev Index (U : Cᵒᵖ) : Type w := Σ i : ℤ, {s : S.sheaf.obj.obj U // S.HasDegree U s i}

/-- Equality of indices is decidable, classically. -/
noncomputable instance (U : Cᵒᵖ) : DecidableEq (S.Index U) := Classical.decEq _

/-- The index attached to a local section of a given degree. -/
abbrev index {U : Cᵒᵖ} (s : S.sheaf.obj.obj U) {n : ℤ} (hs : S.HasDegree U s n) : S.Index U :=
  ⟨n, s, hs⟩

section Index

variable {S}

/-- Restriction of indices along a morphism of the site. -/
abbrev Index.map {U V : Cᵒᵖ} (f : U ⟶ V) (p : S.Index U) : S.Index V :=
  ⟨p.1, S.sheaf.obj.map f p.2.1, S.hasDegree_map f p.2.2⟩

/-- Two indices of the same degree agree as soon as their sections do. -/
theorem Index.mk_eq {U : Cᵒᵖ} {i : ℤ} {s s' : S.sheaf.obj.obj U} (hs : S.HasDegree U s i)
    (hs' : S.HasDegree U s' i) (h : s = s') : (⟨i, s, hs⟩ : S.Index U) = ⟨i, s', hs'⟩ := by
  subst h; rfl

/-- Restriction of indices along the identity is the identity. -/
theorem Index.map_id {U : Cᵒᵖ} (p : S.Index U) : Index.map (𝟙 U) p = p :=
  Index.mk_eq _ _ (Functor.map_id_apply _ _ _)

/-- Restriction of indices along a composite is the composite of the restrictions. -/
theorem Index.map_comp {U V W : Cᵒᵖ} (f : U ⟶ V) (g : V ⟶ W) (p : S.Index U) :
    Index.map g (Index.map f p) = Index.map (f ≫ g) p :=
  Index.mk_eq _ _ (Functor.map_comp_apply _ _ _ _).symm

end Index

end SheafOfGradedSets

end Stacks

namespace SheafOfModules

open Stacks Stacks.SheafOfGradedSets

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

/-- Transport of a summand along an equality of indices. -/
theorem DirectSum.of_heq {ι : Type*} [DecidableEq ι] {β : ι → Type*}
    [∀ i, AddCommMonoid (β i)] {i j : ι} (h : i = j) (x : β i) (y : β j) (hxy : HEq x y) :
    _root_.DirectSum.of β i x = _root_.DirectSum.of β j y := by
  subst h
  rw [eq_of_heq hxy]

/-- Post-composition of a bilinear map of presheaves of modules with a morphism out of its
target. -/
def postcompBilin {R₀ : Cᵒᵖ ⥤ RingCat.{t}} {M : PresheafOfModules.{w₁} R₀}
    {N : PresheafOfModules.{w₂} R₀} {P Q : PresheafOfModules.{w₃} R₀}
    (β : Stacks.BilinearMap M N P) (g : P ⟶ Q) : Stacks.BilinearMap M N Q where
  app U := AddMonoidHom.mk' (fun x => ((g.app U).hom.toAddMonoidHom).comp (β.app U x))
    (fun x x' => by
      ext y
      change (g.app U) (β.app U (x + x') y) = (g.app U) (β.app U x y) + (g.app U) (β.app U x' y)
      rw [β.map_add_left, map_add])
  map_smul_left U r x y := by
    change (g.app U) (β.app U (r • x) y) = r • (g.app U) (β.app U x y)
    rw [β.map_smul_left, _root_.map_smul]
  map_smul_right U r x y := by
    change (g.app U) (β.app U x (r • y)) = r • (g.app U) (β.app U x y)
    rw [β.map_smul_right, _root_.map_smul]
  naturality {U V} f x y := by
    change Q.map f ((g.app U) (β.app U x y)) = (g.app V) (β.app V (M.map f x) (N.map f y))
    rw [← β.naturality f, ← PresheafOfModules.naturality_apply g f]

/-- The post-composite `postcompBilin β g` sends `(x, y)` to `g (β x y)`. -/
@[simp] theorem postcompBilin_app {R₀ : Cᵒᵖ ⥤ RingCat.{t}} {M : PresheafOfModules.{w₁} R₀}
    {N : PresheafOfModules.{w₂} R₀} {P Q : PresheafOfModules.{w₃} R₀}
    (β : Stacks.BilinearMap M N P) (g : P ⟶ Q) (U : Cᵒᵖ) (x : M.obj U) (y : N.obj U) :
    (postcompBilin β g).app U x y = g.app U (β.app U x y) := rfl

/-- Restriction commutes with transport along an equality of degrees. -/
theorem sectionRestrict_castHom (X : ℤ → SheafOfModules.{w₁} R) {k k' : ℤ} (h : k = k')
    {U V : Cᵒᵖ} (f : U ⟶ V) (x : (X k).val.obj U) :
    sectionRestrict (X k').val f (castHom X h U x) =
      castHom X h V (sectionRestrict (X k).val f x) := by
  subst h; rfl

/-- Transporting the first argument of the multiplication of a graded algebra along an equality
of degrees. -/
theorem GradedAlgebra.mul_castHom_left (A : GradedAlgebra.{t, a} R) {m m' j : ℤ} (h : m = m')
    (h' : m + j = m' + j) (U : Cᵒᵖ) (y : (A.piece m).val.obj U) (c : (A.piece j).val.obj U) :
    (A.mul m' j).app U (castHom A.piece h U y) c =
      castHom A.piece h' U ((A.mul m j).app U y c) := by
  subst h
  exact (eq_of_heq (heq_castHom A.piece h' U _)).symm

/-- Transport along an equality of degrees commutes with a homomorphism of graded modules. -/
theorem GradedModule.app_castHom {A' : GradedAlgebra.{t, a} R}
    {M N : GradedModule.{t, a, w₁} A'} (φ : GradedModule.Hom M N) {k k' : ℤ} (h : k = k')
    (U : Cᵒᵖ) (x : (M.piece k).val.obj U) :
    (φ.app k').val.app U (castHom M.piece h U x) =
      castHom N.piece h U ((φ.app k).val.app U x) := by
  subst h; rfl

/-- The action of a graded module commutes with restriction, with the target type of the
restriction maps written plainly. -/
theorem GradedModule.smul_sectionRestrict {A' : GradedAlgebra.{t, a} R}
    (M : GradedModule.{t, a, w₁} A') (n i : ℤ) {U V : Cᵒᵖ} (f : U ⟶ V)
    (x : (M.piece n).val.obj U) (y : (A'.piece i).val.obj U) :
    sectionRestrict (M.piece (n + i)).val f (M.smul n i U x y) =
      M.smul n i V (sectionRestrict (M.piece n).val f x)
        (sectionRestrict (A'.piece i).val f y) :=
  M.smul_naturality n i f x y

/-- A family of homogeneous local sections of a graded module indexed by a sheaf of graded
sets, compatible with restriction: a homogeneous section of degree `n` for every local section
of `S` of degree `n`. -/
structure GradedGeneratorFamily [HasWeakSheafify J (Type w)] {A : GradedAlgebra.{t, a} R}
    (S : SheafOfGradedSets.{w} J) (M : GradedModule.{t, a, max w a} A) where
  /-- The homogeneous section attached to a local section of `S`. -/
  app (n : ℤ) (U : Cᵒᵖ) (s : S.sheaf.obj.obj U) (h : S.HasDegree U s n) : (M.piece n).val.obj U
  /-- The family is compatible with the restriction maps. -/
  naturality (n : ℤ) {U V : Cᵒᵖ} (f : U ⟶ V) (s : S.sheaf.obj.obj U) (h : S.HasDegree U s n)
      (h' : S.HasDegree V (S.sheaf.obj.map f s) n) :
    (M.piece n).val.map f (app n U s h) = app n V (S.sheaf.obj.map f s) h'

/-- The naturality of a generator family, with the target type of the restriction maps written
plainly. -/
theorem GradedGeneratorFamily.sectionRestrict_app [HasWeakSheafify J (Type w)]
    {A : GradedAlgebra.{t, a} R} {S : SheafOfGradedSets.{w} J}
    {M : GradedModule.{t, a, max w a} A} (g : GradedGeneratorFamily S M) (n : ℤ)
    {U V : Cᵒᵖ} (f : U ⟶ V) (s : S.sheaf.obj.obj U) (h : S.HasDegree U s n)
    (h' : S.HasDegree V (S.sheaf.obj.map f s) n) :
    sectionRestrict (M.piece n).val f (g.app n U s h) =
      g.app n V (S.sheaf.obj.map f s) h' :=
  g.naturality n f s h h'

/-- **Push a family of homogeneous generators along a homomorphism of graded modules.** -/
def GradedGeneratorFamily.map [HasWeakSheafify J (Type w)] {A : GradedAlgebra.{t, a} R}
    {S : SheafOfGradedSets.{w} J} {M M' : GradedModule.{t, a, max w a} A}
    (g : GradedGeneratorFamily S M) (φ : GradedModule.Hom M M') :
    GradedGeneratorFamily S M' where
  app n U s hs := (φ.app n).val.app U (g.app n U s hs)
  naturality n {U V} f s hs hs' :=
    (PresheafOfModules.naturality_apply (φ.app n).val f (g.app n U s hs)).symm.trans
      (congrArg (fun z => (φ.app n).val.app V z) (g.naturality n f s hs hs'))

/-- **Two families of homogeneous generators attaching the same section to every local section
are equal.** -/
theorem GradedGeneratorFamily.ext [HasWeakSheafify J (Type w)] {A : GradedAlgebra.{t, a} R}
    {S : SheafOfGradedSets.{w} J} {M : GradedModule.{t, a, max w a} A}
    {g g' : GradedGeneratorFamily S M}
    (h : ∀ (n : ℤ) (U : Cᵒᵖ) (s : S.sheaf.obj.obj U) (hs : S.HasDegree U s n),
      g.app n U s hs = g'.app n U s hs) : g = g' := by
  obtain ⟨a, ha⟩ := g
  obtain ⟨b, hb⟩ := g'
  obtain rfl : a = b := by
    funext n U s hs
    exact h n U s hs
  rfl

/-- The section a pushed family attaches to a local section. -/
@[simp] theorem GradedGeneratorFamily.map_app [HasWeakSheafify J (Type w)]
    {A : GradedAlgebra.{t, a} R} {S : SheafOfGradedSets.{w} J}
    {M M' : GradedModule.{t, a, max w a} A} (g : GradedGeneratorFamily S M)
    (φ : GradedModule.Hom M M') (n : ℤ) (U : Cᵒᵖ) (s : S.sheaf.obj.obj U)
    (hs : S.HasDegree U s n) :
    (g.map φ).app n U s hs = (φ.app n).val.app U (g.app n U s hs) :=
  rfl

/-- The unit of `A`, transported to degree `j - j`, still acts as a left identity. -/
theorem GradedAlgebra.mul_one_cast (A : GradedAlgebra.{t, a} R) (j m : ℤ) (U : Cᵒᵖ)
    (a : (A.piece m).val.obj U) :
    HEq ((A.mul (j - j) m).app U
        (castHom A.piece (sub_self j).symm U (A.one.eval U)) a) a :=
  (heq_of_eq (A.mul_castHom_left (sub_self j).symm (by omega) U (A.one.eval U) a)).trans
    ((heq_castHom A.piece (by omega) U _).trans (A.one_mul m U a))

/-- The extension to the sheafification of a morphism `φ` into a sheaf restricts to `φ` along the
unit of the sheafification. -/
private theorem sheafifyHomEquiv'_symm_app_toSheafify [HasWeakSheafify J AddCommGrpCat.{w₁}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{w₁}] {P : PresheafOfModules.{w₁} R.obj}
    {Z : SheafOfModules.{w₁} R} (φ : P ⟶ Z.val) (U : Cᵒᵖ) (ζ : P.obj U) :
    ((PresheafOfModules.sheafifyHomEquiv' (𝟙 R.obj) (CategoryTheory.toSheafify J P.presheaf)
      Z.isSheaf).symm φ).app U ((CategoryTheory.toSheafify J P.presheaf).app U ζ) = φ.app U ζ :=
  congrArg (fun ψ : P.presheaf ⟶ Z.val.presheaf => ψ.app U ζ)
    (PresheafOfModules.comp_toPresheaf_map_sheafifyHomEquiv'_symm_hom (𝟙 R.obj)
      (CategoryTheory.toSheafify J P.presheaf) Z.isSheaf φ)

section CoefficientPresentation

variable [HasWeakSheafify J (Type w)] (S : SheafOfGradedSets.{w} J)
  (X : ℤ → SheafOfModules.{a} R)

/-- The sections of the presentation of `X[S]` in degree `n`: the direct sum, over the
homogeneous local sections `s` of `S`, of the shifted pieces `X^{n - deg s}`. -/
abbrev coeffSections (n : ℤ) (U : Cᵒᵖ) : Type max w a :=
  ⨁ p : S.Index U, ((X (n - p.1)).val.obj U : Type a)

/-- The summand of the presentation of `X[S]` indexed by a homogeneous local section `s` of
degree `i`. -/
noncomputable abbrev coeffOf (n : ℤ) (U : Cᵒᵖ) (i : ℤ) (s : S.sheaf.obj.obj U)
    (hs : S.HasDegree U s i) (x : (X (n - i)).val.obj U) : coeffSections S X n U :=
  _root_.DirectSum.of _ ⟨i, s, hs⟩ x

/-- The summands of the presentation only depend on the data they display. -/
theorem coeffOf_congr (n : ℤ) (U : Cᵒᵖ) (i : ℤ) {s s' : S.sheaf.obj.obj U}
    (hs : S.HasDegree U s i) (hs' : S.HasDegree U s' i)
    {x y : (X (n - i)).val.obj U} (h : s = s') (hxy : x = y) :
    coeffOf S X n U i s hs x = coeffOf S X n U i s' hs' y := by
  subst h; subst hxy; rfl

/-- The inclusion of a summand of the presentation of `X[S]` is additive. -/
theorem coeffOf_add (n : ℤ) (U : Cᵒᵖ) (i : ℤ) (s : S.sheaf.obj.obj U)
    (hs : S.HasDegree U s i) (x y : (X (n - i)).val.obj U) :
    coeffOf S X n U i s hs (x + y) =
      coeffOf S X n U i s hs x + coeffOf S X n U i s hs y :=
  map_add (_root_.DirectSum.of (fun q : S.Index U => ((X (n - q.1)).val.obj U : Type a))
    ⟨i, s, hs⟩) x y

/-- The inclusion of a summand of the presentation of `X[S]` is `R`-linear. -/
theorem coeffOf_smul (n : ℤ) (U : Cᵒᵖ) (i : ℤ) (s : S.sheaf.obj.obj U)
    (hs : S.HasDegree U s i) (r : R.obj.obj U) (x : (X (n - i)).val.obj U) :
    coeffOf S X n U i s hs (r • x) = r • coeffOf S X n U i s hs x :=
  (_root_.DirectSum.lof (R.obj.obj U) (S.Index U)
    (fun q => ((X (n - q.1)).val.obj U : Type a)) ⟨i, s, hs⟩).map_smul r x

/-- The inclusion of a summand of the presentation of `X[S]` sends zero to zero. -/
theorem coeffOf_zero (n : ℤ) (U : Cᵒᵖ) (i : ℤ) (s : S.sheaf.obj.obj U)
    (hs : S.HasDegree U s i) : coeffOf S X n U i s hs 0 = 0 :=
  map_zero (_root_.DirectSum.of
    (fun q : S.Index U => ((X (n - q.1)).val.obj U : Type a)) ⟨i, s, hs⟩)

/-- The restriction map of the presentation, as an additive map. -/
noncomputable def coeffRestrict (n : ℤ) {U V : Cᵒᵖ} (f : U ⟶ V) :
    coeffSections S X n U →+ coeffSections S X n V :=
  _root_.DirectSum.toAddMonoid fun p =>
    (_root_.DirectSum.of (fun q : S.Index V => ((X (n - q.1)).val.obj V : Type a))
      (Index.map f p)).comp (sectionRestrict (X (n - p.1)).val f)

/-- Restriction sends the summand `s · x` of the presentation of `X[S]` to `s|_V · x|_V`. -/
@[simp] theorem coeffRestrict_coeffOf (n : ℤ) {U V : Cᵒᵖ} (f : U ⟶ V) (i : ℤ)
    (s : S.sheaf.obj.obj U) (hs : S.HasDegree U s i) (x : (X (n - i)).val.obj U) :
    coeffRestrict S X n f (coeffOf S X n U i s hs x) =
      coeffOf S X n V i (S.sheaf.obj.map f s) (S.hasDegree_map f hs)
        (sectionRestrict (X (n - i)).val f x) :=
  _root_.DirectSum.toAddMonoid_of _ _ _

/-- Two additive maps out of the presentation agree as soon as they agree on the summands. -/
theorem coeffSections_addHom_ext {n : ℤ} {U : Cᵒᵖ} {G : Type*} [AddCommMonoid G]
    {φ ψ : coeffSections S X n U →+ G}
    (h : ∀ (i : ℤ) (s : S.sheaf.obj.obj U) (hs : S.HasDegree U s i)
      (x : (X (n - i)).val.obj U),
      φ (coeffOf S X n U i s hs x) = ψ (coeffOf S X n U i s hs x)) : φ = ψ :=
  _root_.DirectSum.addHom_ext fun p x => by obtain ⟨i, s, hs⟩ := p; exact h i s hs x

/-- An induction principle for sections of the presentation. -/
theorem coeffSections_induction {n : ℤ} {U : Cᵒᵖ} {P : coeffSections S X n U → Prop}
    (hzero : P 0)
    (hof : ∀ (i : ℤ) (s : S.sheaf.obj.obj U) (hs : S.HasDegree U s i)
      (x : (X (n - i)).val.obj U), P (coeffOf S X n U i s hs x))
    (hadd : ∀ m m', P m → P m' → P (m + m')) (m : coeffSections S X n U) : P m := by
  induction m using _root_.DirectSum.induction_on with
  | zero => exact hzero
  | of p x => obtain ⟨i, s, hs⟩ := p; exact hof i s hs x
  | add m m' hm hm' => exact hadd m m' hm hm'

/-- The presentation of `X[S]` in degree `n`, as a presheaf of abelian groups. -/
noncomputable def coeffAb (n : ℤ) : Cᵒᵖ ⥤ AddCommGrpCat.{max w a} where
  obj U := AddCommGrpCat.of (coeffSections S X n U)
  map {_ _} f := AddCommGrpCat.ofHom (coeffRestrict S X n f)
  map_id U := by
    ext : 1
    refine coeffSections_addHom_ext S X fun i s hs x => ?_
    change coeffRestrict S X n (𝟙 U) (coeffOf S X n U i s hs x) = coeffOf S X n U i s hs x
    rw [coeffRestrict_coeffOf]
    exact coeffOf_congr S X n U i _ hs (Functor.map_id_apply S.sheaf.obj U s)
      (sectionRestrict_id _ _ x)
  map_comp {U V W} f g := by
    ext : 1
    refine coeffSections_addHom_ext S X fun i s hs x => ?_
    change coeffRestrict S X n (f ≫ g) (coeffOf S X n U i s hs x) =
      coeffRestrict S X n g (coeffRestrict S X n f (coeffOf S X n U i s hs x))
    rw [coeffRestrict_coeffOf, coeffRestrict_coeffOf, coeffRestrict_coeffOf]
    exact coeffOf_congr S X n W i _ _ (Functor.map_comp_apply S.sheaf.obj f g s)
      (sectionRestrict_comp _ f g x)

/-- The sections of `coeffAb S X n` are an `R`-module. -/
noncomputable instance coeffAbModule (n : ℤ) (U : Cᵒᵖ) :
    Module (R.obj.obj U) ((coeffAb S X n).obj U) :=
  inferInstanceAs (Module (R.obj.obj U) (coeffSections S X n U))

/-- Restriction in the presentation of `X[S]` is semilinear along the restriction of `R`. -/
theorem coeffRestrict_smul (n : ℤ) {U V : Cᵒᵖ} (f : U ⟶ V) (r : R.obj.obj U)
    (m : coeffSections S X n U) :
    coeffRestrict S X n f (r • m) = R.obj.map f r • coeffRestrict S X n f m := by
  induction m using coeffSections_induction S X with
  | hzero => simp
  | hof i s hs x =>
    rw [← coeffOf_smul, coeffRestrict_coeffOf, coeffRestrict_coeffOf, sectionRestrict_smul,
      coeffOf_smul]
  | hadd m m' hm hm' => rw [smul_add, map_add, map_add, hm, hm', smul_add]

/-- The presentation of the degree-`n` piece of `X[S]`: the presheaf of modules whose sections
over `U` are `⨁_{s ∈ S(U)} s · X^{n - deg s}(U)`. -/
noncomputable def coeffPres (n : ℤ) : PresheafOfModules.{max w a} R.obj :=
  PresheafOfModules.ofPresheaf (coeffAb S X n) fun _ _ f r m => coeffRestrict_smul S X n f r m

/-- The underlying presheaf of abelian groups of the presentation of `X[S]` is
`coeffAb S X n`. -/
@[simp] theorem coeffPres_presheaf (n : ℤ) : (coeffPres S X n).presheaf = coeffAb S X n := rfl

/-- The sections of the presentation over an object of the site are, on the nose, the direct sum
of the shifted pieces of `X` indexed by the homogeneous local sections of `S`. -/
theorem coeffPres_obj (n : ℤ) (U : Cᵒᵖ) :
    (coeffPres S X n).obj U = ModuleCat.of (R.obj.obj U) (coeffSections S X n U) := rfl

/-- Restriction in the presentation of `X[S]` sends the summand `s · x` to `s|_V · x|_V`. -/
@[simp] theorem coeffPres_sectionRestrict_coeffOf (n : ℤ) {U V : Cᵒᵖ} (f : U ⟶ V) (i : ℤ)
    (s : S.sheaf.obj.obj U) (hs : S.HasDegree U s i) (x : (X (n - i)).val.obj U) :
    sectionRestrict (coeffPres S X n) f (coeffOf S X n U i s hs x) =
      coeffOf S X n V i (S.sheaf.obj.map f s) (S.hasDegree_map f hs)
        (sectionRestrict (X (n - i)).val f x) :=
  coeffRestrict_coeffOf S X n f i s hs x

end CoefficientPresentation

section Presentation

variable [HasWeakSheafify J (Type w)] (A : GradedAlgebra.{t, a} R) (S : SheafOfGradedSets.{w} J)

/-- The sections of the presentation of the free graded module in degree `n`: the direct sum,
over the homogeneous local sections `s` of `S`, of the shifted pieces `A^{n - deg s}`. -/
abbrev freeSections (n : ℤ) (U : Cᵒᵖ) : Type max w a :=
  coeffSections S A.piece n U

/-- The summand of the presentation of the free graded module indexed by a homogeneous local
section `s` of degree `i`. -/
noncomputable abbrev freeOf (n : ℤ) (U : Cᵒᵖ) (i : ℤ) (s : S.sheaf.obj.obj U)
    (hs : S.HasDegree U s i) (x : (A.piece (n - i)).val.obj U) : freeSections A S n U :=
  coeffOf S A.piece n U i s hs x

/-- The summands of the presentation only depend on the data they display. -/
theorem freeOf_congr (n : ℤ) (U : Cᵒᵖ) (i : ℤ) {s s' : S.sheaf.obj.obj U}
    (hs : S.HasDegree U s i) (hs' : S.HasDegree U s' i)
    {x y : (A.piece (n - i)).val.obj U} (h : s = s') (hxy : x = y) :
    freeOf A S n U i s hs x = freeOf A S n U i s' hs' y :=
  coeffOf_congr S A.piece n U i hs hs' h hxy

/-- The inclusion of a summand of the presentation is additive. -/
theorem freeOf_add (n : ℤ) (U : Cᵒᵖ) (i : ℤ) (s : S.sheaf.obj.obj U)
    (hs : S.HasDegree U s i) (x y : (A.piece (n - i)).val.obj U) :
    freeOf A S n U i s hs (x + y) = freeOf A S n U i s hs x + freeOf A S n U i s hs y :=
  coeffOf_add S A.piece n U i s hs x y

/-- The inclusion of a summand of the presentation is `R`-linear. -/
theorem freeOf_smul (n : ℤ) (U : Cᵒᵖ) (i : ℤ) (s : S.sheaf.obj.obj U)
    (hs : S.HasDegree U s i) (r : R.obj.obj U) (x : (A.piece (n - i)).val.obj U) :
    freeOf A S n U i s hs (r • x) = r • freeOf A S n U i s hs x :=
  coeffOf_smul S A.piece n U i s hs r x

/-- The inclusion of a summand of the presentation sends zero to zero. -/
theorem freeOf_zero (n : ℤ) (U : Cᵒᵖ) (i : ℤ) (s : S.sheaf.obj.obj U)
    (hs : S.HasDegree U s i) : freeOf A S n U i s hs 0 = 0 :=
  coeffOf_zero S A.piece n U i s hs

/-- The inclusion of a summand of the presentation commutes with integer multiples. -/
theorem freeOf_zsmul (n : ℤ) (U : Cᵒᵖ) (i : ℤ) (s : S.sheaf.obj.obj U)
    (hs : S.HasDegree U s i) (k : ℤ) (x : (A.piece (n - i)).val.obj U) :
    freeOf A S n U i s hs (k • x) = k • freeOf A S n U i s hs x :=
  AddMonoidHom.map_zsmul _ _ _

/-- The restriction map of the presentation, as an additive map. -/
noncomputable def freeRestrict (n : ℤ) {U V : Cᵒᵖ} (f : U ⟶ V) :
    freeSections A S n U →+ freeSections A S n V :=
  coeffRestrict S A.piece n f

/-- Restriction sends the summand `s · x` to `s|_V · x|_V`. -/
@[simp] theorem freeRestrict_freeOf (n : ℤ) {U V : Cᵒᵖ} (f : U ⟶ V) (i : ℤ)
    (s : S.sheaf.obj.obj U) (hs : S.HasDegree U s i) (x : (A.piece (n - i)).val.obj U) :
    freeRestrict A S n f (freeOf A S n U i s hs x) =
      freeOf A S n V i (S.sheaf.obj.map f s) (S.hasDegree_map f hs)
        (sectionRestrict (A.piece (n - i)).val f x) :=
  coeffRestrict_coeffOf S A.piece n f i s hs x

/-- Two additive maps out of the presentation agree as soon as they agree on the summands. -/
theorem freeSections_addHom_ext {n : ℤ} {U : Cᵒᵖ} {G : Type*} [AddCommMonoid G]
    {φ ψ : freeSections A S n U →+ G}
    (h : ∀ (i : ℤ) (s : S.sheaf.obj.obj U) (hs : S.HasDegree U s i)
      (x : (A.piece (n - i)).val.obj U),
      φ (freeOf A S n U i s hs x) = ψ (freeOf A S n U i s hs x)) : φ = ψ :=
  coeffSections_addHom_ext S A.piece h

/-- An induction principle for sections of the presentation. -/
theorem freeSections_induction {n : ℤ} {U : Cᵒᵖ} {P : freeSections A S n U → Prop}
    (hzero : P 0)
    (hof : ∀ (i : ℤ) (s : S.sheaf.obj.obj U) (hs : S.HasDegree U s i)
      (x : (A.piece (n - i)).val.obj U), P (freeOf A S n U i s hs x))
    (hadd : ∀ m m', P m → P m' → P (m + m')) (m : freeSections A S n U) : P m :=
  coeffSections_induction S A.piece hzero hof hadd m

/-- The presentation of the free graded module, as a presheaf of abelian groups. -/
noncomputable def freeAb (n : ℤ) : Cᵒᵖ ⥤ AddCommGrpCat.{max w a} :=
  coeffAb S A.piece n

/-- The sections of `freeAb A S n` are an `R`-module. -/
noncomputable instance freeAbModule (n : ℤ) (U : Cᵒᵖ) :
    Module (R.obj.obj U) ((freeAb A S n).obj U) :=
  coeffAbModule S A.piece n U

/-- Restriction in the presentation is semilinear along the restriction of `R`. -/
theorem freeRestrict_smul (n : ℤ) {U V : Cᵒᵖ} (f : U ⟶ V) (r : R.obj.obj U)
    (m : freeSections A S n U) :
    freeRestrict A S n f (r • m) = R.obj.map f r • freeRestrict A S n f m :=
  coeffRestrict_smul S A.piece n f r m

/-- The presentation of the degree-`n` part of the free graded module: the presheaf of modules
whose sections over `U` are `⨁_{s ∈ S(U)} s · A^{n - deg s}(U)`. -/
noncomputable def freePres (n : ℤ) : PresheafOfModules.{max w a} R.obj :=
  coeffPres S A.piece n

/-- The underlying presheaf of abelian groups of the presentation is `freeAb A S n`. -/
@[simp] theorem freePres_presheaf (n : ℤ) : (freePres A S n).presheaf = freeAb A S n :=
  coeffPres_presheaf S A.piece n

/-- The sections of the presentation over an object of the site are, on the nose, the direct
sum of the shifted pieces of `A` indexed by the homogeneous local sections of `S`. -/
theorem freePres_obj (n : ℤ) (U : Cᵒᵖ) :
    (freePres A S n).obj U = ModuleCat.of (R.obj.obj U) (freeSections A S n U) :=
  coeffPres_obj S A.piece n U

/-- Restriction in the presentation sends the summand `s · x` to `s|_V · x|_V`. -/
@[simp] theorem freePres_sectionRestrict_freeOf (n : ℤ) {U V : Cᵒᵖ} (f : U ⟶ V) (i : ℤ)
    (s : S.sheaf.obj.obj U) (hs : S.HasDegree U s i) (x : (A.piece (n - i)).val.obj U) :
    sectionRestrict (freePres A S n) f (freeOf A S n U i s hs x) =
      freeOf A S n V i (S.sheaf.obj.map f s) (S.hasDegree_map f hs)
        (sectionRestrict (A.piece (n - i)).val f x) :=
  coeffPres_sectionRestrict_coeffOf S A.piece n f i s hs x

/-- The degree bookkeeping of the action: a generator of degree `j` contributes `A^{n - j}` in
total degree `n`, and multiplying by a section of `A^i` lands in total degree `n + i`. -/
theorem freeDeg (n i j : ℤ) : n - j + i = n + i - j := by omega

/-- The degree of a generator plus the degree of its coefficient is the total degree. -/
theorem freeDegAdd (n j : ℤ) : j + (n - j) = n := by omega

/-- The action of a homogeneous section of `A` on one summand of the presentation. -/
noncomputable def presActComp (n i : ℤ) (U : Cᵒᵖ) (p : S.Index U) :
    ((A.piece (n - p.1)).val.obj U : Type a) →+
      ((A.piece i).val.obj U →+ freeSections A S (n + i) U) :=
  AddMonoidHom.mk'
    (fun x => AddMonoidHom.mk'
      (fun b => freeOf A S (n + i) U p.1 p.2.1 p.2.2
        (castHom A.piece (freeDeg n i p.1) U ((A.mul (n - p.1) i).app U x b)))
      (fun b b' => by rw [map_add, map_add, freeOf_add]))
    (fun x x' => by
      ext b : 1
      change freeOf A S (n + i) U p.1 p.2.1 p.2.2
          (castHom A.piece (freeDeg n i p.1) U ((A.mul (n - p.1) i).app U (x + x') b)) = _
      rw [(A.mul (n - p.1) i).map_add_left, map_add, freeOf_add]
      rfl)

/-- The action of homogeneous sections of `A` on the presentation. -/
noncomputable def presAct (n i : ℤ) (U : Cᵒᵖ) :
    freeSections A S n U →+ ((A.piece i).val.obj U →+ freeSections A S (n + i) U) :=
  _root_.DirectSum.toAddMonoid fun p => presActComp A S n i U p

/-- A section `b` of `A` acts on the summand `s · x` of the presentation as `s · (x b)`. -/
@[simp] theorem presAct_freeOf (n i : ℤ) (U : Cᵒᵖ) (j : ℤ) (s : S.sheaf.obj.obj U)
    (hs : S.HasDegree U s j) (x : (A.piece (n - j)).val.obj U)
    (b : (A.piece i).val.obj U) :
    presAct A S n i U (freeOf A S n U j s hs x) b =
      freeOf A S (n + i) U j s hs
        (castHom A.piece (freeDeg n i j) U ((A.mul (n - j) i).app U x b)) := by
  change (_root_.DirectSum.toAddMonoid (fun p => presActComp A S n i U p)
    (freeOf A S n U j s hs x)) b = _
  rw [_root_.DirectSum.toAddMonoid_of]
  rfl

/-- The action of `A` on the presentation is `R`-linear in the section of the presentation. -/
theorem presAct_smul_left (n i : ℤ) (U : Cᵒᵖ) (r : R.obj.obj U) (ξ : freeSections A S n U)
    (b : (A.piece i).val.obj U) :
    presAct A S n i U (r • ξ) b = r • presAct A S n i U ξ b := by
  induction ξ using freeSections_induction A S with
  | hzero => simp
  | hof j s hs x =>
    rw [← freeOf_smul, presAct_freeOf, presAct_freeOf, (A.mul (n - j) i).map_smul_left,
      castHom_smul, freeOf_smul]
  | hadd ξ ξ' hξ hξ' => simp only [smul_add, map_add, AddMonoidHom.add_apply, hξ, hξ']

/-- The action of `A` on the presentation is `R`-linear in the section of `A`. -/
theorem presAct_smul_right (n i : ℤ) (U : Cᵒᵖ) (r : R.obj.obj U) (ξ : freeSections A S n U)
    (b : (A.piece i).val.obj U) :
    presAct A S n i U ξ (r • b) = r • presAct A S n i U ξ b := by
  induction ξ using freeSections_induction A S with
  | hzero => simp
  | hof j s hs x =>
    rw [presAct_freeOf, presAct_freeOf, (A.mul (n - j) i).map_smul_right, castHom_smul,
      freeOf_smul]
  | hadd ξ ξ' hξ hξ' => simp only [map_add, AddMonoidHom.add_apply, hξ, hξ', smul_add]

/-- The action on the presentation commutes with multiplication by an integer in the module
variable. -/
theorem presAct_zsmul_left (n i : ℤ) (U : Cᵒᵖ) (k : ℤ) (ζ : freeSections A S n U)
    (b : (A.piece i).val.obj U) :
    presAct A S n i U (k • ζ) b = k • presAct A S n i U ζ b := by
  rw [AddMonoidHom.map_zsmul]; rfl

/-- The action of `A` on the presentation commutes with restriction. -/
theorem presAct_naturality (n i : ℤ) {U V : Cᵒᵖ} (f : U ⟶ V) (ξ : freeSections A S n U)
    (b : (A.piece i).val.obj U) :
    freeRestrict A S (n + i) f (presAct A S n i U ξ b) =
      presAct A S n i V (freeRestrict A S n f ξ) (sectionRestrict (A.piece i).val f b) := by
  induction ξ using freeSections_induction A S with
  | hzero => simp
  | hof j s hs x =>
    rw [presAct_freeOf, freeRestrict_freeOf, freeRestrict_freeOf, presAct_freeOf,
      sectionRestrict_castHom]
    exact freeOf_congr A S (n + i) V j _ _ rfl
      (congrArg (castHom A.piece (freeDeg n i j) V) ((A.mul (n - j) i).naturality f x b))
  | hadd ξ ξ' hξ hξ' => simp only [map_add, AddMonoidHom.add_apply, hξ, hξ']

/-- The action of homogeneous sections of `A` on the presentation, as a bilinear map. -/
noncomputable def presActBilin (n i : ℤ) :
    Stacks.BilinearMap (freePres A S n) (A.piece i).val (freePres A S (n + i)) where
  app U := presAct A S n i U
  map_smul_left U r x y := presAct_smul_left A S n i U r x y
  map_smul_right U r x y := presAct_smul_right A S n i U r x y
  naturality {_ _} f x y := presAct_naturality A S n i f x y

/-- Transport of sections of the presentation along an equality of degrees. -/
noncomputable def freeCast {k k' : ℤ} (h : k = k') (U : Cᵒᵖ) :
    freeSections A S k U →+ freeSections A S k' U := by
  subst h; exact AddMonoidHom.id _

/-- Transport along the reflexive equality of degrees is the identity. -/
theorem freeCast_rfl {k : ℤ} (U : Cᵒᵖ) (ζ : freeSections A S k U) :
    freeCast A S (rfl : k = k) U ζ = ζ := rfl

/-- A section of the presentation is heterogeneously equal to its transport. -/
theorem heq_freeCast {k k' : ℤ} (h : k = k') (U : Cᵒᵖ) (ζ : freeSections A S k U) :
    HEq (freeCast A S h U ζ) ζ := by subst h; rfl

/-- Heterogeneously equal sections of the presentation have equal transports to a common
degree. -/
theorem freeCast_eq_freeCast {k k' l : ℤ} (h : k = l) (h' : k' = l) (U : Cᵒᵖ)
    {ζ : freeSections A S k U} {ζ' : freeSections A S k' U} (hζ : HEq ζ ζ') :
    freeCast A S h U ζ = freeCast A S h' U ζ' :=
  eq_of_heq ((heq_freeCast A S h U ζ).trans (hζ.trans (heq_freeCast A S h' U ζ').symm))

/-- A section of the presentation is heterogeneously equal to any section equal to its
transport. -/
theorem heq_of_freeCast_eq {k k' : ℤ} (h : k = k') (U : Cᵒᵖ)
    {ζ : freeSections A S k U} {ζ' : freeSections A S k' U} (hζ : freeCast A S h U ζ = ζ') :
    HEq ζ ζ' :=
  (heq_freeCast A S h U ζ).symm.trans (heq_of_eq hζ)

/-- Transport of the summand `s · x` along an equality of degrees is the summand `s · x'`, where
`x'` is the transport of the coefficient `x`. -/
theorem freeCast_freeOf {k k' : ℤ} (h : k = k') (U : Cᵒᵖ) (i : ℤ) (s : S.sheaf.obj.obj U)
    (hs : S.HasDegree U s i) (x : (A.piece (k - i)).val.obj U) (h' : k - i = k' - i) :
    freeCast A S h U (freeOf A S k U i s hs x) =
      freeOf A S k' U i s hs (castHom A.piece h' U x) := by
  subst h
  exact freeOf_congr A S k U i hs hs rfl (eq_of_heq (heq_castHom A.piece h' U x)).symm

/-- Transport of sections of the presentation commutes with multiplication by an integer. -/
theorem freeCast_zsmul {k k' : ℤ} (h : k = k') (U : Cᵒᵖ) (m : ℤ) (ζ : freeSections A S k U) :
    freeCast A S h U (m • ζ) = m • freeCast A S h U ζ :=
  AddMonoidHom.map_zsmul _ _ _

/-- The unit of `A` acts as the identity on the presentation. -/
theorem presAct_one (n : ℤ) (U : Cᵒᵖ) (ζ : (freePres A S n).obj U) :
    freeCast A S (add_zero n) U (presAct A S n 0 U ζ (A.one.eval U)) = ζ := by
  induction ζ using freeSections_induction A S with
  | hzero => simp
  | hof j s hs x =>
    rw [presAct_freeOf, freeCast_freeOf A S (add_zero n) U j s hs _ (by omega),
      Cofree.castHom_castHom]
    exact freeOf_congr A S n U j hs hs rfl
      (eq_of_heq ((heq_castHom A.piece _ U _).trans (A.mul_one (n - j) U x)))
  | hadd ζ ζ' hζ hζ' => simp only [map_add, AddMonoidHom.add_apply, hζ, hζ']

/-- The action on the presentation is associative. -/
theorem presAct_assoc (n i j : ℤ) (U : Cᵒᵖ) (ζ : (freePres A S n).obj U)
    (b : (A.piece i).val.obj U) (c : (A.piece j).val.obj U) :
    freeCast A S (add_assoc n i j) U (presAct A S (n + i) j U (presAct A S n i U ζ b) c) =
      presAct A S n (i + j) U ζ ((A.mul i j).app U b c) := by
  induction ζ using freeSections_induction A S with
  | hzero => simp
  | hof k s hs x =>
    rw [presAct_freeOf, presAct_freeOf,
      freeCast_freeOf A S (add_assoc n i j) U k s hs _ (by omega), presAct_freeOf,
      Cofree.castHom_castHom, A.mul_castHom_left (freeDeg n i k) (by omega), Cofree.castHom_castHom]
    refine freeOf_congr A S (n + (i + j)) U k hs hs rfl ?_
    exact Cofree.castHom_eq_castHom _ _ U (A.mul_assoc (n - k) i j U x b c)
  | hadd ζ ζ' hζ hζ' => simp only [map_add, AddMonoidHom.add_apply, hζ, hζ']

section Lift

variable (N : GradedModule.{t, a, max w a} A) (g : GradedGeneratorFamily S N)

/-- The map from the presentation to a graded module determined by a family of generators. -/
noncomputable def liftAdd (n : ℤ) (U : Cᵒᵖ) :
    freeSections A S n U →+ ((N.piece n).val.obj U : Type max w a) :=
  _root_.DirectSum.toAddMonoid fun p =>
    AddMonoidHom.mk'
      (fun x => castHom N.piece (freeDegAdd n p.1) U
        (N.smul p.1 (n - p.1) U (g.app p.1 U p.2.1 p.2.2) x))
      (fun x y => by rw [map_add, map_add])

/-- The lift of a generator family `g` sends the summand `s · x` to `g s` acted on by `x`. -/
@[simp] theorem liftAdd_freeOf (n : ℤ) (U : Cᵒᵖ) (j : ℤ) (s : S.sheaf.obj.obj U)
    (hs : S.HasDegree U s j) (x : (A.piece (n - j)).val.obj U) :
    liftAdd A S N g n U (freeOf A S n U j s hs x) =
      castHom N.piece (freeDegAdd n j) U (N.smul j (n - j) U (g.app j U s hs) x) :=
  _root_.DirectSum.toAddMonoid_of _ _ _

/-- The lift of a generator family to the presentation is `R`-linear. -/
theorem liftAdd_smul (n : ℤ) (U : Cᵒᵖ) (r : R.obj.obj U) (ζ : freeSections A S n U) :
    liftAdd A S N g n U (r • ζ) = r • liftAdd A S N g n U ζ := by
  induction ζ using freeSections_induction A S with
  | hzero => simp
  | hof j s hs x =>
    rw [← freeOf_smul, liftAdd_freeOf, liftAdd_freeOf, N.smul_smul_right, castHom_smul]
  | hadd ζ ζ' hζ hζ' => rw [smul_add, map_add, map_add, hζ, hζ', smul_add]

/-- The lift of a generator family to the presentation commutes with restriction. -/
theorem liftAdd_naturality (n : ℤ) {U V : Cᵒᵖ} (f : U ⟶ V) (ζ : freeSections A S n U) :
    liftAdd A S N g n V (freeRestrict A S n f ζ) =
      sectionRestrict (N.piece n).val f (liftAdd A S N g n U ζ) := by
  induction ζ using freeSections_induction A S with
  | hzero => simp
  | hof j s hs x =>
    rw [freeRestrict_freeOf, liftAdd_freeOf, liftAdd_freeOf, sectionRestrict_castHom,
      N.smul_sectionRestrict, g.sectionRestrict_app j f s hs (S.hasDegree_map f hs)]
  | hadd ζ ζ' hζ hζ' => simp only [map_add, hζ, hζ']

/-- The morphism of presheaves of modules from the presentation to a graded module determined
by a family of generators. -/
noncomputable def liftPres (n : ℤ) : freePres A S n ⟶ (N.piece n).val where
  app U := ModuleCat.ofHom
    { toFun := fun ζ => liftAdd A S N g n U ζ
      map_add' := fun ζ ζ' => map_add (liftAdd A S N g n U) ζ ζ'
      map_smul' := fun r ζ => liftAdd_smul A S N g n U r ζ }
  naturality f := ModuleCat.hom_ext (LinearMap.ext fun ζ => liftAdd_naturality A S N g n f ζ)

/-- The components of `liftPres` are `liftAdd`. -/
@[simp] theorem liftPres_app (n : ℤ) (U : Cᵒᵖ) (ζ : freeSections A S n U) :
    (liftPres A S N g n).app U ζ = liftAdd A S N g n U ζ := rfl

/-- The lift is compatible with the action of `A`, at the level of the presentation. -/
theorem liftAdd_presAct (n i : ℤ) (U : Cᵒᵖ) (ζ : freeSections A S n U)
    (b : (A.piece i).val.obj U) :
    liftAdd A S N g (n + i) U (presAct A S n i U ζ b) =
      N.smul n i U (liftAdd A S N g n U ζ) b := by
  induction ζ using freeSections_induction A S with
  | hzero => simp
  | hof j s hs x =>
    rw [presAct_freeOf, liftAdd_freeOf, liftAdd_freeOf,
      Cofree.smul_castHom_right N (freeDeg n i j), Cofree.smul_castHom_left N (freeDegAdd n j),
      Cofree.castHom_castHom]
    exact Cofree.castHom_eq_castHom _ _ U (N.smul_mul j (n - j) i U (g.app j U s hs) x b).symm
  | hadd ζ ζ' hζ hζ' => simp only [map_add, AddMonoidHom.add_apply, hζ, hζ']

end Lift

end Presentation

/-- The degree bookkeeping of the differential. -/
theorem dDeg (n j : ℤ) : n - j + 1 = n + 1 - j := by omega

/-- The differential of `A` commutes with transport along an equality of degrees. -/
theorem algD_castHom (D : DifferentialGradedAlgebra.{t, a} R) {k k' : ℤ} (h : k = k')
    (h' : k + 1 = k' + 1) (U : Cᵒᵖ) (z : (D.complex.X k).val.obj U) :
    homSections (D.complex.d k' (k' + 1)) U (castHom D.toGradedAlgebra.piece h U z) =
      castHom D.toGradedAlgebra.piece h' U (homSections (D.complex.d k (k + 1)) U z) := by
  subst h
  exact (eq_of_heq (heq_castHom D.toGradedAlgebra.piece h' U _)).symm

/-- The signed Leibniz rule of a sheaf of differential graded algebras, with its two transports
written through `SheafOfModules.castHom` and its degree family spelled as the pieces of the
underlying sheaf of graded algebras. This is the form the free module consumes. -/
theorem algD_mul (D : DifferentialGradedAlgebra.{t, a} R) (n i : ℤ) (U : Cᵒᵖ)
    (x : (D.toGradedAlgebra.piece n).val.obj U) (y : (D.toGradedAlgebra.piece i).val.obj U) :
    homSections (D.complex.d (n + i) (n + i + 1)) U ((D.toGradedAlgebra.mul n i).app U x y) =
      castHom D.toGradedAlgebra.piece (add_right_comm n 1 i) U
          ((D.toGradedAlgebra.mul (n + 1) i).app U (homSections (D.complex.d n (n + 1)) U x) y)
        + (Int.negOnePow n : ℤ) • castHom D.toGradedAlgebra.piece (add_assoc n i 1).symm U
            ((D.toGradedAlgebra.mul n (i + 1)).app U x
              (homSections (D.complex.d i (i + 1)) U y)) := by
  simp only [castHom_apply]
  exact D.leibniz n i U x y

section Differential

variable [HasWeakSheafify J (Type w)] (S : SheafOfGradedSets.{w} J)
  (D : DifferentialGradedAlgebra.{t, a} R)

/-- The differential of the presentation of `A[S]`: the generators are closed, so the Leibniz
rule forces `d (s · a) = (-1)^{deg s} s · d a`. -/
noncomputable def dPres (n : ℤ) (U : Cᵒᵖ) :
    freeSections D.toGradedAlgebra S n U →+ freeSections D.toGradedAlgebra S (n + 1) U :=
  _root_.DirectSum.toAddMonoid fun p =>
    AddMonoidHom.mk'
      (fun x => (Int.negOnePow p.1 : ℤ) • freeOf D.toGradedAlgebra S (n + 1) U p.1 p.2.1 p.2.2
        (castHom D.toGradedAlgebra.piece (dDeg n p.1) U
          (homSections (D.complex.d (n - p.1) (n - p.1 + 1)) U x)))
      (fun x y => by rw [map_add, map_add, freeOf_add, smul_add])

/-- The differential of the presentation on a summand: `d (s · x) = (-1)^{deg s} s · d x`. -/
@[simp] theorem dPres_freeOf (n : ℤ) (U : Cᵒᵖ) (j : ℤ) (s : S.sheaf.obj.obj U)
    (hs : S.HasDegree U s j) (x : (D.complex.X (n - j)).val.obj U) :
    dPres S D n U (freeOf D.toGradedAlgebra S n U j s hs x) =
      (Int.negOnePow j : ℤ) • freeOf D.toGradedAlgebra S (n + 1) U j s hs
        (castHom D.toGradedAlgebra.piece (dDeg n j) U
          (homSections (D.complex.d (n - j) (n - j + 1)) U x)) :=
  _root_.DirectSum.toAddMonoid_of _ _ _

/-- The differential of the presentation is `R`-linear. -/
theorem dPres_smul (n : ℤ) (U : Cᵒᵖ) (r : R.obj.obj U)
    (ζ : freeSections D.toGradedAlgebra S n U) :
    dPres S D n U (r • ζ) = r • dPres S D n U ζ := by
  induction ζ using freeSections_induction D.toGradedAlgebra S with
  | hzero => simp
  | hof j s hs x =>
    rw [← freeOf_smul, dPres_freeOf, dPres_freeOf, homSections_smul, castHom_smul, freeOf_smul,
      smul_comm]
  | hadd ζ ζ' hζ hζ' => rw [smul_add, map_add, map_add, hζ, hζ', smul_add]

/-- The differential of the presentation commutes with restriction. -/
theorem dPres_naturality (n : ℤ) {U V : Cᵒᵖ} (f : U ⟶ V)
    (ζ : freeSections D.toGradedAlgebra S n U) :
    dPres S D n V (freeRestrict D.toGradedAlgebra S n f ζ) =
      freeRestrict D.toGradedAlgebra S (n + 1) f (dPres S D n U ζ) := by
  induction ζ using freeSections_induction D.toGradedAlgebra S with
  | hzero => simp
  | hof j s hs x =>
    rw [freeRestrict_freeOf, dPres_freeOf, dPres_freeOf, AddMonoidHom.map_zsmul,
      freeRestrict_freeOf, sectionRestrict_castHom]
    refine congrArg (fun z => (Int.negOnePow j : ℤ) • z) ?_
    refine freeOf_congr D.toGradedAlgebra S (n + 1) V j _ _ rfl ?_
    exact congrArg (fun z => castHom D.toGradedAlgebra.piece (dDeg n j) V z)
      (homSections_naturality (D.complex.d (n - j) (n - j + 1)) f x).symm
  | hadd ζ ζ' hζ hζ' => simp only [map_add, hζ, hζ']

/-- The differential of the presentation squares to zero. -/
theorem dPres_dPres (n : ℤ) (U : Cᵒᵖ) (ζ : freeSections D.toGradedAlgebra S n U) :
    dPres S D (n + 1) U (dPres S D n U ζ) = 0 := by
  induction ζ using freeSections_induction D.toGradedAlgebra S with
  | hzero => simp
  | hof j s hs x =>
    rw [dPres_freeOf, AddMonoidHom.map_zsmul, dPres_freeOf,
      algD_castHom D (dDeg n j) (by omega) U, Cofree.algD_algD (A := D) (n - j) U x]
    simp
  | hadd ζ ζ' hζ hζ' => rw [map_add, map_add, hζ, hζ', add_zero]

/-- **The Leibniz rule on the presentation.** The generators are closed, so the signed Leibniz
rule of the algebra propagates to the presentation of the free module: the differential of
`ζ · b` is `(d ζ) · b` corrected by `(-1)^n ζ · (d b)`, in the degrees that forces. -/
theorem dPres_presAct (n i : ℤ) (U : Cᵒᵖ) (ζ : freeSections D.toGradedAlgebra S n U)
    (b : (D.toGradedAlgebra.piece i).val.obj U) :
    dPres S D (n + i) U (presAct D.toGradedAlgebra S n i U ζ b) =
      freeCast D.toGradedAlgebra S (add_right_comm n 1 i) U
          (presAct D.toGradedAlgebra S (n + 1) i U (dPres S D n U ζ) b)
        + (Int.negOnePow n : ℤ) • freeCast D.toGradedAlgebra S (add_assoc n i 1).symm U
            (presAct D.toGradedAlgebra S n (i + 1) U ζ
              (homSections (D.complex.d i (i + 1)) U b)) := by
  induction ζ using freeSections_induction D.toGradedAlgebra S with
  | hzero => simp only [map_zero, AddMonoidHom.zero_apply, smul_zero, add_zero]
  | hof j s hs x =>
    have hsign : (Int.negOnePow j : ℤ) * (Int.negOnePow (n - j) : ℤ) = (Int.negOnePow n : ℤ) := by
      rw [← Units.val_mul, ← Int.negOnePow_add, freeDegAdd n j]
    rw [presAct_freeOf, dPres_freeOf, dPres_freeOf, presAct_zsmul_left, presAct_freeOf,
      GradedAlgebra.mul_castHom_left D.toGradedAlgebra (dDeg n j) (by omega) U,
      algD_castHom D (freeDeg n i j) (by omega) U, presAct_freeOf, freeCast_zsmul,
      freeCast_freeOf D.toGradedAlgebra S (add_right_comm n 1 i) U j s hs _ (by omega),
      freeCast_freeOf D.toGradedAlgebra S (add_assoc n i 1).symm U j s hs _ (by omega),
      algD_mul D (n - j) i U x b]
    simp only [map_add, map_zsmul, Cofree.castHom_castHom]
    rw [smul_add, smul_smul, hsign]
  | hadd ζ ζ' hζ hζ' =>
    simp only [map_add, AddMonoidHom.add_apply, hζ, hζ', smul_add]
    abel

/-- The differential of the presentation, as a morphism of presheaves of modules. -/
noncomputable def dPresHom (n : ℤ) :
    freePres D.toGradedAlgebra S n ⟶ freePres D.toGradedAlgebra S (n + 1) where
  app U := ModuleCat.ofHom
    { toFun := fun ζ => dPres S D n U ζ
      map_add' := fun ζ ζ' => map_add (dPres S D n U) ζ ζ'
      map_smul' := fun r ζ => dPres_smul S D n U r ζ }
  naturality f := ModuleCat.hom_ext (LinearMap.ext fun ζ => dPres_naturality S D n f ζ)

/-- The components of `dPresHom` are `dPres`. -/
@[simp] theorem dPresHom_app (n : ℤ) (U : Cᵒᵖ) (ζ : freeSections D.toGradedAlgebra S n U) :
    (dPresHom S D n).app U ζ = dPres S D n U ζ := rfl

end Differential

section CoefficientSheafify

variable [HasWeakSheafify J (Type w)] [HasWeakSheafify J AddCommGrpCat.{max w a}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max w a}] (S : SheafOfGradedSets.{w} J)

/-- The degree-`n` piece of `X[S]`: the sheafification of the presentation. -/
noncomputable def coeffPiece (X : ℤ → SheafOfModules.{a} R) (n : ℤ) :
    SheafOfModules.{max w a} R :=
  (PresheafOfModules.sheafification (𝟙 R.obj)).obj (coeffPres S X n)

/-- The canonical morphism from the presentation to the degree-`n` piece of `X[S]`. -/
noncomputable def coeffUnit (X : ℤ → SheafOfModules.{a} R) (n : ℤ) :
    coeffPres S X n ⟶ (coeffPiece S X n).val :=
  PresheafOfModules.toSheafify (𝟙 R.obj)
    (CategoryTheory.toSheafify J (coeffPres S X n).presheaf)

/-- The morphism from the presentation of `X[S]` to its sheafification is locally
surjective. -/
instance (X : ℤ → SheafOfModules.{a} R) (n : ℤ) :
    PresheafOfModules.IsLocallySurjective J (coeffUnit S X n) :=
  inferInstanceAs (PresheafOfModules.IsLocallySurjective J
    (PresheafOfModules.toSheafify (𝟙 R.obj) _))

/-- The morphism from the presentation of `X[S]` to its sheafification is locally
injective. -/
instance (X : ℤ → SheafOfModules.{a} R) (n : ℤ) :
    PresheafOfModules.IsLocallyInjective J (coeffUnit S X n) :=
  inferInstanceAs (PresheafOfModules.IsLocallyInjective J
    (PresheafOfModules.toSheafify (𝟙 R.obj) _))

/-- **Two morphisms out of a piece of `X[S]` which agree on the image of the presentation are
equal.** -/
theorem coeffPiece_hom_ext {X : ℤ → SheafOfModules.{a} R} {Z : SheafOfModules.{max w a} R}
    {n : ℤ} {φ ψ : coeffPiece S X n ⟶ Z}
    (h : ∀ (U : Cᵒᵖ) (ζ : (coeffPres S X n).obj U),
      φ.val.app U ((coeffUnit S X n).app U ζ) = ψ.val.app U ((coeffUnit S X n).app U ζ)) :
    φ = ψ := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  refine Stacks.eq_of_forall_lift Z.isSheaf.isSeparated (coeffUnit S X n) x _ _ ?_
  intro Y f m hm
  change sectionRestrict Z.val f (φ.val.app U x) = sectionRestrict Z.val f (ψ.val.app U x)
  calc sectionRestrict Z.val f (φ.val.app U x)
      = φ.val.app Y (sectionRestrict (coeffPiece S X n).val f x) :=
        (PresheafOfModules.naturality_apply φ.val f x).symm
    _ = φ.val.app Y ((coeffUnit S X n).app Y m) := congrArg (fun z => φ.val.app Y z) hm.symm
    _ = ψ.val.app Y ((coeffUnit S X n).app Y m) := h Y m
    _ = ψ.val.app Y (sectionRestrict (coeffPiece S X n).val f x) :=
        congrArg (fun z => ψ.val.app Y z) hm
    _ = sectionRestrict Z.val f (ψ.val.app U x) :=
        PresheafOfModules.naturality_apply ψ.val f x

end CoefficientSheafify

section Sheafify

variable [HasWeakSheafify J (Type w)] [HasWeakSheafify J AddCommGrpCat.{max w a}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max w a}]
  (A : GradedAlgebra.{t, a} R) (S : SheafOfGradedSets.{w} J)

/-- The degree-`n` piece of the free graded module `A[S]`: the sheafification of the
presentation. -/
noncomputable def freePiece (n : ℤ) : SheafOfModules.{max w a} R :=
  coeffPiece S A.piece n

/-- The degree-`n` piece of `A[S]` is the sheafification of the presentation. -/
theorem freePiece_eq (n : ℤ) :
    freePiece A S n = (PresheafOfModules.sheafification (𝟙 R.obj)).obj (freePres A S n) := rfl

/-- The canonical morphism from the presentation to the degree-`n` piece of `A[S]`. -/
noncomputable def freeUnit (n : ℤ) : freePres A S n ⟶ (freePiece A S n).val :=
  coeffUnit S A.piece n

/-- The morphism from the presentation to its sheafification is locally surjective. -/
instance (n : ℤ) : PresheafOfModules.IsLocallySurjective J (freeUnit A S n) :=
  inferInstanceAs (PresheafOfModules.IsLocallySurjective J (coeffUnit S A.piece n))

/-- The morphism from the presentation to its sheafification is locally injective. -/
instance (n : ℤ) : PresheafOfModules.IsLocallyInjective J (freeUnit A S n) :=
  inferInstanceAs (PresheafOfModules.IsLocallyInjective J (coeffUnit S A.piece n))

/-- The underlying presheaf of abelian groups of a piece of `A[S]` is a sheaf. -/
theorem freePiece_isSheaf (n : ℤ) : Presheaf.IsSheaf J (freePiece A S n).val.presheaf :=
  (freePiece A S n).isSheaf

/-- The morphism `freeUnit` is, on sections, the unit of the sheafification of the underlying
presheaf of abelian groups. -/
theorem freeUnit_app_eq (n : ℤ) (U : Cᵒᵖ) (ζ : freeSections A S n U) :
    (freeUnit A S n).app U ζ =
      (CategoryTheory.toSheafify J (freePres A S n).presheaf).app U ζ := rfl

/-- Transport along an equality of degrees commutes with the morphism to the sheafification. -/
theorem freeUnit_heq {k k' : ℤ} (h : k = k') (U : Cᵒᵖ) {ζ : freeSections A S k U}
    {ζ' : freeSections A S k' U} (hζ : HEq ζ ζ') :
    HEq ((freeUnit A S k).app U ζ) ((freeUnit A S k').app U ζ') := by
  subst h
  rw [eq_of_heq hζ]


/-- Transport along an equality of degrees commutes with the map to the sheafification. -/
theorem castHom_freeUnit {k k' : ℤ} (h : k = k') (U : Cᵒᵖ) (ζ : (freePres A S k).obj U) :
    castHom (freePiece A S) h U ((freeUnit A S k).app U ζ) =
      (freeUnit A S k').app U (freeCast A S h U ζ) := by
  subst h; rfl

/-- The map to the sheafification is additive, with its source written as a direct sum. -/
theorem freeUnit_add (n : ℤ) (U : Cᵒᵖ) (ζ ζ' : freeSections A S n U) :
    (freeUnit A S n).app U (ζ + ζ') =
      (freeUnit A S n).app U ζ + (freeUnit A S n).app U ζ' :=
  map_add ((freeUnit A S n).app U).hom ζ ζ'

/-- The map to the sheafification commutes with multiplication by an integer. -/
theorem freeUnit_zsmul (n : ℤ) (U : Cᵒᵖ) (k : ℤ) (ζ : freeSections A S n U) :
    (freeUnit A S n).app U (k • ζ) = k • (freeUnit A S n).app U ζ :=
  map_zsmul ((freeUnit A S n).app U).hom k ζ

/-- **Two morphisms out of a piece of `A[S]` which agree on the image of the presentation are
equal.** The piece is the sheafification of the presentation and the map to it is locally
surjective, so a morphism out of it into any sheaf of modules is determined by its restriction
to the presentation. -/
theorem freePiece_hom_ext {Z : SheafOfModules.{max w a} R} {n : ℤ}
    {φ ψ : freePiece A S n ⟶ Z}
    (h : ∀ (U : Cᵒᵖ) (ζ : (freePres A S n).obj U),
      φ.val.app U ((freeUnit A S n).app U ζ) = ψ.val.app U ((freeUnit A S n).app U ζ)) :
    φ = ψ :=
  coeffPiece_hom_ext S h

/-- The action of homogeneous sections of `A` on the degree-`n` piece of `A[S]`: the unique
extension to the sheafification of the action on the presentation. -/
noncomputable def freeActBilin (n i : ℤ) :
    Stacks.BilinearMap (freePiece A S n).val (A.piece i).val (freePiece A S (n + i)).val :=
  Stacks.BilinearMap.extend (freePiece A S (n + i)).isSheaf (freeUnit A S n)
    (postcompBilin (presActBilin A S n i) (freeUnit A S (n + i)))

/-- On the image of the presentation, the action `freeActBilin` is the image of the action
`presAct` on the presentation. -/
@[simp] theorem freeActBilin_unit (n i : ℤ) (U : Cᵒᵖ) (ζ : (freePres A S n).obj U)
    (b : (A.piece i).val.obj U) :
    (freeActBilin A S n i).app U ((freeUnit A S n).app U ζ) b =
      (freeUnit A S (n + i)).app U (presAct A S n i U ζ b) :=
  Stacks.BilinearMap.extendVal_app (freePiece A S (n + i)).isSheaf (freeUnit A S n)
    (postcompBilin (presActBilin A S n i) (freeUnit A S (n + i))) ζ b

/-- The value of the action of `A` on `A[S]`, computed on a local lift of its module argument
to the presentation. -/
theorem freeActBilin_lift (n i : ℤ) (U : Cᵒᵖ) (x : (freePiece A S n).val.obj U)
    (b : (A.piece i).val.obj U) {Y : Cᵒᵖ} (f : U ⟶ Y) (m : (freePres A S n).obj Y)
    (hm : (freeUnit A S n).app Y m = (freePiece A S n).val.map f x) :
    sectionRestrict (freePiece A S (n + i)).val f ((freeActBilin A S n i).app U x b) =
      (freeUnit A S (n + i)).app Y
        (presAct A S n i Y m (sectionRestrict (A.piece i).val f b)) :=
  ((freeActBilin A S n i).naturality f x b).trans
    ((congrArg (fun z => (freeActBilin A S n i).app Y z
        (sectionRestrict (A.piece i).val f b)) hm).symm.trans
      (freeActBilin_unit A S n i Y m (sectionRestrict (A.piece i).val f b)))

/-- The unit of `A` acts as the identity on `A[S]`. -/
theorem freeActBilin_one (n : ℤ) (U : Cᵒᵖ) (x : (freePiece A S n).val.obj U) :
    HEq ((freeActBilin A S n 0).app U x (A.one.eval U)) x := by
  refine Cofree.heq_of_castHom_eq (X := freePiece A S) (add_zero n) U ?_
  refine Stacks.eq_of_forall_lift (freePiece A S n).isSheaf.isSeparated (freeUnit A S n) x _ _ ?_
  intro Y f m hm
  calc sectionRestrict (freePiece A S n).val f
        (castHom (freePiece A S) (add_zero n) U ((freeActBilin A S n 0).app U x (A.one.eval U)))
      = castHom (freePiece A S) (add_zero n) Y (sectionRestrict (freePiece A S (n + 0)).val f
          ((freeActBilin A S n 0).app U x (A.one.eval U))) :=
        sectionRestrict_castHom (freePiece A S) (add_zero n) f _
    _ = castHom (freePiece A S) (add_zero n) Y ((freeUnit A S (n + 0)).app Y
          (presAct A S n 0 Y m (sectionRestrict (A.piece 0).val f (A.one.eval U)))) :=
        congrArg (fun z => castHom (freePiece A S) (add_zero n) Y z)
          (freeActBilin_lift A S n 0 U x (A.one.eval U) f m hm)
    _ = castHom (freePiece A S) (add_zero n) Y
          ((freeUnit A S (n + 0)).app Y (presAct A S n 0 Y m (A.one.eval Y))) :=
        congrArg (fun z => castHom (freePiece A S) (add_zero n) Y
          ((freeUnit A S (n + 0)).app Y (presAct A S n 0 Y m z)))
          (PresheafOfModules.sections_property A.one f)
    _ = (freeUnit A S n).app Y
          (freeCast A S (add_zero n) Y (presAct A S n 0 Y m (A.one.eval Y))) :=
        castHom_freeUnit A S (add_zero n) Y _
    _ = (freeUnit A S n).app Y m :=
        congrArg (fun z => (freeUnit A S n).app Y z) (presAct_one A S n Y m)
    _ = sectionRestrict (freePiece A S n).val f x := hm

/-- The action of `A` on `A[S]` is associative. -/
theorem freeActBilin_assoc (n i j : ℤ) (U : Cᵒᵖ) (x : (freePiece A S n).val.obj U)
    (b : (A.piece i).val.obj U) (c : (A.piece j).val.obj U) :
    HEq ((freeActBilin A S (n + i) j).app U ((freeActBilin A S n i).app U x b) c)
      ((freeActBilin A S n (i + j)).app U x ((A.mul i j).app U b c)) := by
  refine Cofree.heq_of_castHom_eq (X := freePiece A S) (add_assoc n i j) U ?_
  refine Stacks.eq_of_forall_lift (freePiece A S (n + (i + j))).isSheaf.isSeparated
    (freeUnit A S n) x _ _ ?_
  intro Y f m hm
  have hlift := freeActBilin_lift A S n i U x b f m hm
  have hmul : (A.mul i j).app Y (sectionRestrict (A.piece i).val f b)
        (sectionRestrict (A.piece j).val f c) =
      sectionRestrict (A.piece (i + j)).val f ((A.mul i j).app U b c) :=
    ((A.mul i j).naturality f b c).symm
  change sectionRestrict (freePiece A S (n + (i + j))).val f
      (castHom (freePiece A S) (add_assoc n i j) U
        ((freeActBilin A S (n + i) j).app U ((freeActBilin A S n i).app U x b) c)) =
    sectionRestrict (freePiece A S (n + (i + j))).val f
      ((freeActBilin A S n (i + j)).app U x ((A.mul i j).app U b c))
  calc sectionRestrict (freePiece A S (n + (i + j))).val f
        (castHom (freePiece A S) (add_assoc n i j) U
          ((freeActBilin A S (n + i) j).app U ((freeActBilin A S n i).app U x b) c))
      = castHom (freePiece A S) (add_assoc n i j) Y
          (sectionRestrict (freePiece A S (n + i + j)).val f
            ((freeActBilin A S (n + i) j).app U ((freeActBilin A S n i).app U x b) c)) :=
        sectionRestrict_castHom (freePiece A S) (add_assoc n i j) f _
    _ = castHom (freePiece A S) (add_assoc n i j) Y ((freeUnit A S (n + i + j)).app Y
          (presAct A S (n + i) j Y (presAct A S n i Y m (sectionRestrict (A.piece i).val f b))
            (sectionRestrict (A.piece j).val f c))) :=
        congrArg (fun z => castHom (freePiece A S) (add_assoc n i j) Y z)
          (freeActBilin_lift A S (n + i) j U ((freeActBilin A S n i).app U x b) c f
            (presAct A S n i Y m (sectionRestrict (A.piece i).val f b)) hlift.symm)
    _ = (freeUnit A S (n + (i + j))).app Y (freeCast A S (add_assoc n i j) Y
          (presAct A S (n + i) j Y (presAct A S n i Y m (sectionRestrict (A.piece i).val f b))
            (sectionRestrict (A.piece j).val f c))) := castHom_freeUnit A S (add_assoc n i j) Y _
    _ = (freeUnit A S (n + (i + j))).app Y (presAct A S n (i + j) Y m
          ((A.mul i j).app Y (sectionRestrict (A.piece i).val f b)
            (sectionRestrict (A.piece j).val f c))) :=
        congrArg (fun z => (freeUnit A S (n + (i + j))).app Y z)
          (presAct_assoc A S n i j Y m (sectionRestrict (A.piece i).val f b)
            (sectionRestrict (A.piece j).val f c))
    _ = (freeUnit A S (n + (i + j))).app Y (presAct A S n (i + j) Y m
          (sectionRestrict (A.piece (i + j)).val f ((A.mul i j).app U b c))) :=
        congrArg (fun z => (freeUnit A S (n + (i + j))).app Y
          (presAct A S n (i + j) Y m z)) hmul
    _ = sectionRestrict (freePiece A S (n + (i + j))).val f
          ((freeActBilin A S n (i + j)).app U x ((A.mul i j).app U b c)) :=
        (freeActBilin_lift A S n (i + j) U x ((A.mul i j).app U b c) f m hm).symm

/-- **The free graded `A`-module on a sheaf of graded sets.** Its degree-`n` piece is the
sheafification of `U ↦ ⨁_{s ∈ S(U)} s · A^{n - deg s}(U)`. -/
@[sga "4 II 6.8" "more general"]
noncomputable def freeGradedModule : GradedModule.{t, a, max w a} A where
  piece := freePiece A S
  smul n i U := (freeActBilin A S n i).app U
  smul_smul_left n i U r x y := (freeActBilin A S n i).map_smul_left U r x y
  smul_smul_right n i U r x y := (freeActBilin A S n i).map_smul_right U r x y
  smul_naturality n i {_ _} f x y := (freeActBilin A S n i).naturality f x y
  smul_mul n i j U x y z := freeActBilin_assoc A S n i j U x y z
  smul_one n U x := freeActBilin_one A S n U x

/-- The degree-`n` piece of `A[S]` is `freePiece A S n`. -/
@[simp] theorem freeGradedModule_piece (n : ℤ) : (freeGradedModule A S).piece n =
    freePiece A S n := rfl

/-- The action of `A` on `A[S]` is `freeActBilin`. -/
@[simp] theorem freeGradedModule_smul (n i : ℤ) (U : Cᵒᵖ) :
    (freeGradedModule A S).smul n i U = (freeActBilin A S n i).app U := rfl


/-- The canonical generator of `A[S]` attached to a homogeneous local section of `S`. -/
noncomputable def freeGeneratorSection (n : ℤ) (U : Cᵒᵖ) (s : S.sheaf.obj.obj U)
    (hs : S.HasDegree U s n) : (freePiece A S n).val.obj U :=
  (freeUnit A S n).app U
    (freeOf A S n U n s hs (castHom A.piece (sub_self n).symm U (A.one.eval U)))

/-- **The generators of `A[S]` are a basis of the presentation**: the generator attached to a
local section `s` of degree `n` is the image of the summand `s · 1`. -/
theorem freeGeneratorSection_eq (n : ℤ) (U : Cᵒᵖ) (s : S.sheaf.obj.obj U)
    (hs : S.HasDegree U s n) :
    freeGeneratorSection A S n U s hs = (freeUnit A S n).app U
      (freeOf A S n U n s hs (castHom A.piece (sub_self n).symm U (A.one.eval U))) := rfl

/-- The canonical generators of `A[S]`: one homogeneous generator for every homogeneous local
section of `S`. -/
noncomputable def freeGenerator : GradedGeneratorFamily S (freeGradedModule A S) where
  app n U s hs := freeGeneratorSection A S n U s hs
  naturality n {U V} f s hs hs' :=
    (PresheafOfModules.naturality_apply (freeUnit A S n) f
        (freeOf A S n U n s hs (castHom A.piece (sub_self n).symm U (A.one.eval U)))).symm.trans
      (congrArg (fun z => (freeUnit A S n).app V z)
        ((freeRestrict_freeOf A S n f n s hs _).trans
          (freeOf_congr A S n V n (S.hasDegree_map f hs) hs' rfl
            ((sectionRestrict_castHom A.piece (sub_self n).symm f _).trans
              (congrArg (fun z => castHom A.piece (sub_self n).symm V z)
                (PresheafOfModules.sections_property A.one f))))))

/-- **The action of `A` on a generator of `A[S]`.** -/
theorem freeActBilin_generator (n m : ℤ) (U : Cᵒᵖ) (s : S.sheaf.obj.obj U)
    (hs : S.HasDegree U s n) (a : (A.piece m).val.obj U) (h : m = n + m - n) :
    (freeActBilin A S n m).app U (freeGeneratorSection A S n U s hs) a =
      (freeUnit A S (n + m)).app U
        (freeOf A S (n + m) U n s hs (castHom A.piece h U a)) :=
  (freeActBilin_unit A S n m U
      (freeOf A S n U n s hs (castHom A.piece (sub_self n).symm U (A.one.eval U))) a).trans
    (congrArg (fun z => (freeUnit A S (n + m)).app U z)
      ((presAct_freeOf A S n m U n s hs _ a).trans
        (freeOf_congr A S (n + m) U n hs hs rfl
          (Cofree.castHom_eq_castHom _ _ U (A.mul_one_cast n m U a)))))

/-- Every summand of the presentation is a generator acted on by a homogeneous section of
`A`. -/
theorem freeUnit_freeOf (n j : ℤ) (U : Cᵒᵖ) (s : S.sheaf.obj.obj U)
    (hs : S.HasDegree U s j) (x : (A.piece (n - j)).val.obj U) (h : j + (n - j) = n) :
    castHom (freePiece A S) h U
        ((freeActBilin A S j (n - j)).app U (freeGeneratorSection A S j U s hs) x) =
      (freeUnit A S n).app U (freeOf A S n U j s hs x) :=
  (congrArg (fun z => castHom (freePiece A S) h U z)
      (freeActBilin_generator A S j (n - j) U s hs x (by omega))).trans
    ((castHom_freeUnit A S h U _).trans
      (congrArg (fun z => (freeUnit A S n).app U z)
        ((freeCast_freeOf A S h U j s hs _ (by omega)).trans
          (freeOf_congr A S n U j hs hs rfl
            ((Cofree.castHom_castHom A.piece _ _ U x).trans
              (eq_of_heq (heq_castHom A.piece _ U x)))))))

section Universal

variable (N : GradedModule.{t, a, max w a} A) (g : GradedGeneratorFamily S N)

/-- The morphism of sheaves of modules from `A[S]` to a graded module determined by a family
of generators. -/
noncomputable def liftVal (n : ℤ) : freePiece A S n ⟶ N.piece n :=
  ⟨(PresheafOfModules.sheafifyHomEquiv' (𝟙 R.obj)
      (CategoryTheory.toSheafify J (freePres A S n).presheaf) (N.piece n).isSheaf).symm
    (liftPres A S N g n)⟩

/-- On the image of the presentation, `liftVal` is `liftAdd`. -/
theorem liftVal_unit (n : ℤ) (U : Cᵒᵖ) (ζ : (freePres A S n).obj U) :
    (liftVal A S N g n).val.app U ((freeUnit A S n).app U ζ) =
      liftAdd A S N g n U ζ :=
  sheafifyHomEquiv'_symm_app_toSheafify (liftPres A S N g n) U ζ

/-- **The lift of a family of generators to a homomorphism out of `A[S]`.** -/
noncomputable def liftHom : GradedModule.Hom (freeGradedModule A S) N where
  app n := liftVal A S N g n
  map_smul n i U x y := by
    refine Stacks.eq_of_forall_lift (N.piece (n + i)).isSheaf.isSeparated
      (freeUnit A S n) x _ _ ?_
    intro Y f m hm
    change sectionRestrict (N.piece (n + i)).val f
        ((liftVal A S N g (n + i)).val.app U ((freeActBilin A S n i).app U x y)) =
      sectionRestrict (N.piece (n + i)).val f (N.smul n i U ((liftVal A S N g n).val.app U x) y)
    calc sectionRestrict (N.piece (n + i)).val f
          ((liftVal A S N g (n + i)).val.app U ((freeActBilin A S n i).app U x y))
        = (liftVal A S N g (n + i)).val.app Y
            (sectionRestrict (freePiece A S (n + i)).val f
              ((freeActBilin A S n i).app U x y)) :=
          (PresheafOfModules.naturality_apply (liftVal A S N g (n + i)).val f _).symm
      _ = (liftVal A S N g (n + i)).val.app Y ((freeUnit A S (n + i)).app Y
            (presAct A S n i Y m (sectionRestrict (A.piece i).val f y))) :=
          congrArg (fun z => (liftVal A S N g (n + i)).val.app Y z)
            (freeActBilin_lift A S n i U x y f m hm)
      _ = liftAdd A S N g (n + i) Y (presAct A S n i Y m
            (sectionRestrict (A.piece i).val f y)) :=
          liftVal_unit A S N g (n + i) Y _
      _ = N.smul n i Y (liftAdd A S N g n Y m) (sectionRestrict (A.piece i).val f y) :=
          liftAdd_presAct A S N g n i Y m _
      _ = N.smul n i Y ((liftVal A S N g n).val.app Y ((freeUnit A S n).app Y m))
            (sectionRestrict (A.piece i).val f y) :=
          congrArg (fun z => N.smul n i Y z (sectionRestrict (A.piece i).val f y))
            (liftVal_unit A S N g n Y m).symm
      _ = N.smul n i Y ((liftVal A S N g n).val.app Y
            (sectionRestrict (freePiece A S n).val f x))
            (sectionRestrict (A.piece i).val f y) :=
          congrArg (fun z => N.smul n i Y ((liftVal A S N g n).val.app Y z)
            (sectionRestrict (A.piece i).val f y)) hm
      _ = N.smul n i Y (sectionRestrict (N.piece n).val f
            ((liftVal A S N g n).val.app U x)) (sectionRestrict (A.piece i).val f y) :=
          congrArg (fun z => N.smul n i Y z (sectionRestrict (A.piece i).val f y))
            (PresheafOfModules.naturality_apply (liftVal A S N g n).val f x)
      _ = sectionRestrict (N.piece (n + i)).val f
            (N.smul n i U ((liftVal A S N g n).val.app U x) y) :=
          (N.smul_sectionRestrict n i f _ y).symm

/-- **The lift sends each generator of `A[S]` to the prescribed section.** -/
theorem liftHom_generator (n : ℤ) (U : Cᵒᵖ) (s : S.sheaf.obj.obj U)
    (hs : S.HasDegree U s n) :
    ((liftHom A S N g).app n).val.app U (freeGeneratorSection A S n U s hs) =
      g.app n U s hs :=
  (liftVal_unit A S N g n U _).trans
    ((liftAdd_freeOf A S N g n U n s hs _).trans
      ((congrArg (fun z => castHom N.piece (freeDegAdd n n) U z)
          (Cofree.smul_castHom_right N (sub_self n).symm U (g.app n U s hs)
            (A.one.eval U))).trans
        ((Cofree.castHom_castHom N.piece _ _ U _).trans
          (eq_of_heq ((heq_castHom N.piece _ U _).trans
            (N.smul_one n U (g.app n U s hs)))))))

/-- The composite of the map to the sheafification with a homomorphism out of `A[S]`, as an
additive map on the sections of the presentation. -/
noncomputable abbrev unitComp (f : GradedModule.Hom (freeGradedModule A S) N) (n : ℤ)
    (U : Cᵒᵖ) : freeSections A S n U →+ ((N.piece n).val.obj U : Type max w a) :=
  (((f.app n).val.app U).hom.toAddMonoidHom).comp
    (((freeUnit A S n).app U).hom.toAddMonoidHom)

/-- Two homomorphisms out of `A[S]` which agree on the generators agree on the image of the
presentation. -/
theorem hom_app_freeUnit {f₁ f₂ : GradedModule.Hom (freeGradedModule A S) N}
    (h : ∀ (n : ℤ) (U : Cᵒᵖ) (s : S.sheaf.obj.obj U) (hs : S.HasDegree U s n),
      (f₁.app n).val.app U (freeGeneratorSection A S n U s hs) =
        (f₂.app n).val.app U (freeGeneratorSection A S n U s hs))
    (n : ℤ) (U : Cᵒᵖ) (ζ : freeSections A S n U) :
    (f₁.app n).val.app U ((freeUnit A S n).app U ζ) =
      (f₂.app n).val.app U ((freeUnit A S n).app U ζ) := by
  refine DFunLike.congr_fun (freeSections_addHom_ext A S
    (φ := unitComp A S N f₁ n U) (ψ := unitComp A S N f₂ n U) ?_) ζ
  intro j s hs x
  refine Eq.trans (congrArg (fun z => (f₁.app n).val.app U z)
    (freeUnit_freeOf A S n j U s hs x (freeDegAdd n j)).symm) ?_
  refine Eq.trans (GradedModule.app_castHom f₁ (freeDegAdd n j) U _) ?_
  refine Eq.trans (congrArg (fun z => castHom N.piece (freeDegAdd n j) U z)
    (f₁.map_smul j (n - j) U (freeGeneratorSection A S j U s hs) x)) ?_
  refine Eq.trans (congrArg (fun z => castHom N.piece (freeDegAdd n j) U
    (N.smul j (n - j) U z x)) (h j U s hs)) ?_
  refine Eq.trans ?_ (congrArg (fun z => (f₂.app n).val.app U z)
    (freeUnit_freeOf A S n j U s hs x (freeDegAdd n j)))
  refine Eq.trans ?_ (GradedModule.app_castHom f₂ (freeDegAdd n j) U _).symm
  exact (congrArg (fun z => castHom N.piece (freeDegAdd n j) U z)
    (f₂.map_smul j (n - j) U (freeGeneratorSection A S j U s hs) x)).symm

/-- **Two homomorphisms out of `A[S]` agreeing on the generators are equal.** -/
theorem freeGradedModule_hom_ext {f₁ f₂ : GradedModule.Hom (freeGradedModule A S) N}
    (h : ∀ (n : ℤ) (U : Cᵒᵖ) (s : S.sheaf.obj.obj U) (hs : S.HasDegree U s n),
      (f₁.app n).val.app U (freeGeneratorSection A S n U s hs) =
        (f₂.app n).val.app U (freeGeneratorSection A S n U s hs)) : f₁ = f₂ :=
  GradedModule.Hom.ext fun n =>
    freePiece_hom_ext A S fun U ζ => hom_app_freeUnit A S N h n U ζ

/-- **The lift of a family of generators, followed by a homomorphism, is the lift of the pushed
family.** -/
theorem liftHom_comp {M₁ M₂ : GradedModule.{t, a, max w a} A} (g₁ : GradedGeneratorFamily S M₁)
    (φ : GradedModule.Hom M₁ M₂) :
    GradedModule.Hom.comp (liftHom A S M₁ g₁) φ = liftHom A S M₂ (g₁.map φ) :=
  freeGradedModule_hom_ext A S M₂ fun n U s hs =>
    (congrArg (fun z => (φ.app n).val.app U z) (liftHom_generator A S M₁ g₁ n U s hs)).trans
      (liftHom_generator A S M₂ (g₁.map φ) n U s hs).symm

/-- **Every homomorphism out of `A[S]` is the lift of the family of generators it carries.** This
is `freeGradedModule_hom_ext` read as a statement about one homomorphism rather than two. -/
theorem liftHom_map_freeGenerator {M₂ : GradedModule.{t, a, max w a} A}
    (Φ : GradedModule.Hom (freeGradedModule A S) M₂) :
    liftHom A S M₂ ((freeGenerator A S).map Φ) = Φ :=
  freeGradedModule_hom_ext A S M₂ fun n U s hs =>
    liftHom_generator A S M₂ ((freeGenerator A S).map Φ) n U s hs

end Universal




end Sheafify

section DifferentialSheafify

variable [HasWeakSheafify J (Type w)] [HasWeakSheafify J AddCommGrpCat.{max w a}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max w a}]
  (S : SheafOfGradedSets.{w} J) (D : DifferentialGradedAlgebra.{t, a} R)

/-- **The differential of `D[S]`**: the unique extension to the sheafification of the
differential `dPres` of the presentation. -/
noncomputable def freeD (n : ℤ) :
    freePiece D.toGradedAlgebra S n ⟶ freePiece D.toGradedAlgebra S (n + 1) :=
  ⟨(PresheafOfModules.sheafifyHomEquiv' (𝟙 R.obj)
      (CategoryTheory.toSheafify J (freePres D.toGradedAlgebra S n).presheaf)
      (freePiece D.toGradedAlgebra S (n + 1)).isSheaf).symm
    (dPresHom S D n ≫ freeUnit D.toGradedAlgebra S (n + 1))⟩

/-- The differential of `D[S]` restricts to the differential of the presentation. -/
theorem freeD_unit (n : ℤ) (U : Cᵒᵖ) (ζ : (freePres D.toGradedAlgebra S n).obj U) :
    (freeD S D n).val.app U ((freeUnit D.toGradedAlgebra S n).app U ζ) =
      (freeUnit D.toGradedAlgebra S (n + 1)).app U (dPres S D n U ζ) :=
  sheafifyHomEquiv'_symm_app_toSheafify (dPresHom S D n ≫ freeUnit D.toGradedAlgebra S (n + 1))
    U ζ

/-- **The differential of `D[S]` is square-zero.** -/
theorem freeD_freeD (n : ℤ) : freeD S D n ≫ freeD S D (n + 1) = 0 :=
  freePiece_hom_ext D.toGradedAlgebra S fun U ζ =>
    (congrArg (fun z => (freeD S D (n + 1)).val.app U z) (freeD_unit S D n U ζ)).trans
      ((freeD_unit S D (n + 1) U (dPres S D n U ζ)).trans
        ((congrArg (fun z => (freeUnit D.toGradedAlgebra S (n + 1 + 1)).app U z)
            (dPres_dPres S D n U ζ)).trans
          (map_zero ((freeUnit D.toGradedAlgebra S (n + 1 + 1)).app U).hom)))

/-- **The Leibniz rule for the differential of `D[S]`.** -/
theorem freeD_freeActBilin (n i : ℤ) (U : Cᵒᵖ)
    (x : (freePiece D.toGradedAlgebra S n).val.obj U)
    (b : (D.toGradedAlgebra.piece i).val.obj U) :
    (freeD S D (n + i)).val.app U ((freeActBilin D.toGradedAlgebra S n i).app U x b) =
      castHom (freePiece D.toGradedAlgebra S) (add_right_comm n 1 i) U
          ((freeActBilin D.toGradedAlgebra S (n + 1) i).app U ((freeD S D n).val.app U x) b)
        + (Int.negOnePow n : ℤ) •
            castHom (freePiece D.toGradedAlgebra S) (add_assoc n i 1).symm U
              ((freeActBilin D.toGradedAlgebra S n (i + 1)).app U x
                (homSections (D.complex.d i (i + 1)) U b)) := by
  refine Stacks.eq_of_forall_lift
    (freePiece D.toGradedAlgebra S (n + i + 1)).isSheaf.isSeparated
    (freeUnit D.toGradedAlgebra S n) x _ _ ?_
  intro Y f m hm
  have hdx : (freeUnit D.toGradedAlgebra S (n + 1)).app Y (dPres S D n Y m) =
      sectionRestrict (freePiece D.toGradedAlgebra S (n + 1)).val f
        ((freeD S D n).val.app U x) :=
    (freeD_unit S D n Y m).symm.trans
      ((congrArg (fun z => (freeD S D n).val.app Y z) hm).trans
        (PresheafOfModules.naturality_apply (freeD S D n).val f x))
  have hbd : sectionRestrict (D.toGradedAlgebra.piece (i + 1)).val f
        (homSections (D.complex.d i (i + 1)) U b) =
      homSections (D.complex.d i (i + 1)) Y
        (sectionRestrict (D.toGradedAlgebra.piece i).val f b) :=
    homSections_naturality (D.complex.d i (i + 1)) f b
  change sectionRestrict (freePiece D.toGradedAlgebra S (n + i + 1)).val f
      ((freeD S D (n + i)).val.app U ((freeActBilin D.toGradedAlgebra S n i).app U x b)) =
    sectionRestrict (freePiece D.toGradedAlgebra S (n + i + 1)).val f
      (castHom (freePiece D.toGradedAlgebra S) (add_right_comm n 1 i) U
          ((freeActBilin D.toGradedAlgebra S (n + 1) i).app U ((freeD S D n).val.app U x) b)
        + (Int.negOnePow n : ℤ) •
            castHom (freePiece D.toGradedAlgebra S) (add_assoc n i 1).symm U
              ((freeActBilin D.toGradedAlgebra S n (i + 1)).app U x
                (homSections (D.complex.d i (i + 1)) U b)))
  have hL : sectionRestrict (freePiece D.toGradedAlgebra S (n + i + 1)).val f
        ((freeD S D (n + i)).val.app U ((freeActBilin D.toGradedAlgebra S n i).app U x b)) =
      castHom (freePiece D.toGradedAlgebra S) (add_right_comm n 1 i) Y
          ((freeUnit D.toGradedAlgebra S (n + 1 + i)).app Y
            (presAct D.toGradedAlgebra S (n + 1) i Y (dPres S D n Y m)
              (sectionRestrict (D.toGradedAlgebra.piece i).val f b)))
        + (Int.negOnePow n : ℤ) •
            castHom (freePiece D.toGradedAlgebra S) (add_assoc n i 1).symm Y
              ((freeUnit D.toGradedAlgebra S (n + (i + 1))).app Y
                (presAct D.toGradedAlgebra S n (i + 1) Y m
                  (homSections (D.complex.d i (i + 1)) Y
                    (sectionRestrict (D.toGradedAlgebra.piece i).val f b)))) :=
    calc sectionRestrict (freePiece D.toGradedAlgebra S (n + i + 1)).val f
          ((freeD S D (n + i)).val.app U ((freeActBilin D.toGradedAlgebra S n i).app U x b))
        = (freeD S D (n + i)).val.app Y
            (sectionRestrict (freePiece D.toGradedAlgebra S (n + i)).val f
              ((freeActBilin D.toGradedAlgebra S n i).app U x b)) :=
          (PresheafOfModules.naturality_apply (freeD S D (n + i)).val f _).symm
      _ = (freeD S D (n + i)).val.app Y ((freeUnit D.toGradedAlgebra S (n + i)).app Y
            (presAct D.toGradedAlgebra S n i Y m
              (sectionRestrict (D.toGradedAlgebra.piece i).val f b))) :=
          congrArg (fun z => (freeD S D (n + i)).val.app Y z)
            (freeActBilin_lift D.toGradedAlgebra S n i U x b f m hm)
      _ = (freeUnit D.toGradedAlgebra S (n + i + 1)).app Y
            (dPres S D (n + i) Y (presAct D.toGradedAlgebra S n i Y m
              (sectionRestrict (D.toGradedAlgebra.piece i).val f b))) :=
          freeD_unit S D (n + i) Y _
      _ = (freeUnit D.toGradedAlgebra S (n + i + 1)).app Y
            (freeCast D.toGradedAlgebra S (add_right_comm n 1 i) Y
                (presAct D.toGradedAlgebra S (n + 1) i Y (dPres S D n Y m)
                  (sectionRestrict (D.toGradedAlgebra.piece i).val f b))
              + (Int.negOnePow n : ℤ) •
                  freeCast D.toGradedAlgebra S (add_assoc n i 1).symm Y
                    (presAct D.toGradedAlgebra S n (i + 1) Y m
                      (homSections (D.complex.d i (i + 1)) Y
                        (sectionRestrict (D.toGradedAlgebra.piece i).val f b)))) :=
          congrArg (fun z => (freeUnit D.toGradedAlgebra S (n + i + 1)).app Y z)
            (dPres_presAct S D n i Y m (sectionRestrict (D.toGradedAlgebra.piece i).val f b))
      _ = (freeUnit D.toGradedAlgebra S (n + i + 1)).app Y
              (freeCast D.toGradedAlgebra S (add_right_comm n 1 i) Y
                (presAct D.toGradedAlgebra S (n + 1) i Y (dPres S D n Y m)
                  (sectionRestrict (D.toGradedAlgebra.piece i).val f b)))
            + (Int.negOnePow n : ℤ) • (freeUnit D.toGradedAlgebra S (n + i + 1)).app Y
                (freeCast D.toGradedAlgebra S (add_assoc n i 1).symm Y
                  (presAct D.toGradedAlgebra S n (i + 1) Y m
                    (homSections (D.complex.d i (i + 1)) Y
                      (sectionRestrict (D.toGradedAlgebra.piece i).val f b)))) :=
          (freeUnit_add D.toGradedAlgebra S (n + i + 1) Y _ _).trans
            (congrArg (fun z => (freeUnit D.toGradedAlgebra S (n + i + 1)).app Y
                (freeCast D.toGradedAlgebra S (add_right_comm n 1 i) Y
                  (presAct D.toGradedAlgebra S (n + 1) i Y (dPres S D n Y m)
                    (sectionRestrict (D.toGradedAlgebra.piece i).val f b))) + z)
              (freeUnit_zsmul D.toGradedAlgebra S (n + i + 1) Y _ _))
      _ = _ :=
          congrArg₂ (· + ·) (castHom_freeUnit D.toGradedAlgebra S (add_right_comm n 1 i) Y _).symm
            (congrArg (fun z => (Int.negOnePow n : ℤ) • z)
              (castHom_freeUnit D.toGradedAlgebra S (add_assoc n i 1).symm Y _).symm)
  have hR : sectionRestrict (freePiece D.toGradedAlgebra S (n + i + 1)).val f
        (castHom (freePiece D.toGradedAlgebra S) (add_right_comm n 1 i) U
            ((freeActBilin D.toGradedAlgebra S (n + 1) i).app U ((freeD S D n).val.app U x) b)
          + (Int.negOnePow n : ℤ) •
              castHom (freePiece D.toGradedAlgebra S) (add_assoc n i 1).symm U
                ((freeActBilin D.toGradedAlgebra S n (i + 1)).app U x
                  (homSections (D.complex.d i (i + 1)) U b))) =
      castHom (freePiece D.toGradedAlgebra S) (add_right_comm n 1 i) Y
          ((freeUnit D.toGradedAlgebra S (n + 1 + i)).app Y
            (presAct D.toGradedAlgebra S (n + 1) i Y (dPres S D n Y m)
              (sectionRestrict (D.toGradedAlgebra.piece i).val f b)))
        + (Int.negOnePow n : ℤ) •
            castHom (freePiece D.toGradedAlgebra S) (add_assoc n i 1).symm Y
              ((freeUnit D.toGradedAlgebra S (n + (i + 1))).app Y
                (presAct D.toGradedAlgebra S n (i + 1) Y m
                  (homSections (D.complex.d i (i + 1)) Y
                    (sectionRestrict (D.toGradedAlgebra.piece i).val f b)))) := by
    rw [map_add (sectionRestrict (freePiece D.toGradedAlgebra S (n + i + 1)).val f),
      AddMonoidHom.map_zsmul (sectionRestrict (freePiece D.toGradedAlgebra S (n + i + 1)).val f),
      sectionRestrict_castHom (freePiece D.toGradedAlgebra S) (add_right_comm n 1 i) f,
      sectionRestrict_castHom (freePiece D.toGradedAlgebra S) (add_assoc n i 1).symm f,
      freeActBilin_lift D.toGradedAlgebra S (n + 1) i U ((freeD S D n).val.app U x) b f
        (dPres S D n Y m) hdx,
      freeActBilin_lift D.toGradedAlgebra S n (i + 1) U x
        (homSections (D.complex.d i (i + 1)) U b) f m hm, hbd]
  exact hL.trans hR.symm

/-- The underlying cochain complex of the free differential graded module on `S`: the pieces of
`A[S]` for `A` the graded algebra underlying `D`, with the differential `freeD`. -/
noncomputable def freeComplex : CochainComplex (SheafOfModules.{max w a} R) ℤ :=
  CochainComplex.of (freePiece D.toGradedAlgebra S) (freeD S D) (freeD_freeD S D)

/-- **The free differential graded `D`-module on a sheaf of graded sets.** Its underlying graded
module is `D[S]` and its differential is the one for which every canonical generator is
closed. -/
noncomputable def freeDGModule : DifferentialGradedModule.{t, a, max w a} D where
  complex := freeComplex S D
  mul n i := freeActBilin D.toGradedAlgebra S n i
  mul_assoc n i j U x y z := freeActBilin_assoc D.toGradedAlgebra S n i j U x y z
  mul_one n U x := freeActBilin_one D.toGradedAlgebra S n U x
  leibniz n i U x y := by
    rw [show (freeComplex S D).d (n + i) (n + i + 1) = freeD S D (n + i) from
        CochainComplex.of_d _ _ (n + i),
      show (freeComplex S D).d n (n + 1) = freeD S D n from CochainComplex.of_d _ _ n,
      ← castHom_apply, ← castHom_apply]
    exact freeD_freeActBilin S D n i U x y

/-- The degree-`n` term of the complex of `D[S]` is `freePiece D.toGradedAlgebra S n`. -/
@[simp] theorem freeDGModule_complex_X (n : ℤ) :
    (freeDGModule S D).complex.X n = freePiece D.toGradedAlgebra S n := rfl

/-- The multiplication of `D[S]` is the action `freeActBilin` of `D` on `A[S]`. -/
@[simp] theorem freeDGModule_mul (n i : ℤ) :
    (freeDGModule S D).mul n i = freeActBilin D.toGradedAlgebra S n i := rfl

/-- The differential of the complex of `D[S]` from degree `n` to `n + 1` is `freeD S D n`. -/
@[simp] theorem freeDGModule_complex_d (n : ℤ) :
    (freeDGModule S D).complex.d n (n + 1) = freeD S D n :=
  CochainComplex.of_d _ _ n

/-- **The differential graded module `D[S]` has `A[S]` as its underlying graded module**, where
`A` is the graded algebra underlying `D`: the pieces and the action are the same, not merely
isomorphic. This is the degreewise identification together with the identification of the
actions. -/
theorem forgetToGradedModule_freeDGModule :
    (forgetToGradedModule D).obj (freeDGModule S D) = freeGradedModule D.toGradedAlgebra S := rfl

/-- The degree-`n` piece of the differential graded module `D[S]` is the degree-`n` piece of
`A[S]`. -/
theorem freeDGModule_piece (n : ℤ) :
    (freeDGModule S D).complex.X n = (freeGradedModule D.toGradedAlgebra S).piece n := rfl

/-- The action of `D` on the differential graded module `D[S]` is the action of `A` on `A[S]`. -/
theorem freeDGModule_mul_app (n i : ℤ) (U : Cᵒᵖ) :
    ((freeDGModule S D).mul n i).app U = (freeGradedModule D.toGradedAlgebra S).smul n i U := rfl

/-- The action of `D` on `D[S]` and the action of `A` on `A[S]`, compared by `HEq` as the
source states it. The underlying equality `freeDGModule_mul_app` is available and is stronger:
the two degree families agree on the nose, so the two actions have the same type. -/
theorem freeDGModule_mul_heq (n i : ℤ) (U : Cᵒᵖ) :
    HEq (((freeDGModule S D).mul n i).app U)
      ((freeGradedModule D.toGradedAlgebra S).smul n i U) :=
  heq_of_eq (freeDGModule_mul_app S D n i U)

/-- **Every canonical generator of `D[S]` is closed.** This is what pins down the differential:
together with the Leibniz rule it forces `d (s · a) = (-1)^{deg s} s · d a`. -/
theorem freeD_freeGeneratorSection (n : ℤ) (U : Cᵒᵖ) (s : S.sheaf.obj.obj U)
    (hs : S.HasDegree U s n) :
    (freeD S D n).val.app U (freeGeneratorSection D.toGradedAlgebra S n U s hs) = 0 := by
  have h1 : homSections (D.complex.d 0 (0 + 1)) U (D.toGradedAlgebra.one.eval U) = 0 :=
    D.one_closed U
  have h2 : homSections (D.complex.d (n - n) (n - n + 1)) U
        (castHom D.toGradedAlgebra.piece (sub_self n).symm U
          (D.toGradedAlgebra.one.eval U)) = 0 := by
    rw [algD_castHom D (sub_self n).symm (by omega) U, h1, Cofree.castHom_zero]
  have h3 : (Int.negOnePow n : ℤ) • freeOf D.toGradedAlgebra S (n + 1) U n s hs
      (castHom D.toGradedAlgebra.piece (dDeg n n) U
        (homSections (D.complex.d (n - n) (n - n + 1)) U
          (castHom D.toGradedAlgebra.piece (sub_self n).symm U
            (D.toGradedAlgebra.one.eval U)))) = 0 := by
    rw [h2, Cofree.castHom_zero, freeOf_zero, smul_zero]
  refine Eq.trans (congrArg (fun z => (freeD S D n).val.app U z)
    (freeGeneratorSection_eq D.toGradedAlgebra S n U s hs)) ?_
  refine Eq.trans (freeD_unit S D n U _) ?_
  refine Eq.trans (congrArg (fun z => (freeUnit D.toGradedAlgebra S (n + 1)).app U z)
    ((dPres_freeOf S D n U n s hs _).trans h3)) ?_
  exact map_zero ((freeUnit D.toGradedAlgebra S (n + 1)).app U).hom

/-- The canonical generators of `D[S]` are closed, stated for the differential of the cochain
complex as the source's differential graded module field spells it. -/
theorem freeDGModule_d_freeGenerator (n : ℤ) (U : Cᵒᵖ) (s : S.sheaf.obj.obj U)
    (hs : S.HasDegree U s n) :
    ((freeDGModule S D).complex.d n (n + 1)).val.app U
        ((freeGenerator D.toGradedAlgebra S).app n U s hs) = 0 :=
  (congrArg (fun φ : freePiece D.toGradedAlgebra S n ⟶ freePiece D.toGradedAlgebra S (n + 1) =>
      φ.val.app U ((freeGenerator D.toGradedAlgebra S).app n U s hs))
    (freeDGModule_complex_d S D n)).trans (freeD_freeGeneratorSection S D n U s hs)

end DifferentialSheafify

section Bundle

variable [HasWeakSheafify J (Type w)] [HasWeakSheafify J AddCommGrpCat.{max w a}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max w a}]

/-- The free graded `A`-module on a sheaf of graded sets, packaged with everything that
characterizes it. -/
structure FreeGradedModuleData (A : GradedAlgebra.{t, a} R) (S : SheafOfGradedSets.{w} J) where
  /-- The underlying graded `A`-module. -/
  module : GradedModule.{t, a, max w a} A
  /-- The degreewise presentation. -/
  presentation (n : ℤ) : PresheafOfModules.{max w a} R.obj
  /-- Its sections are the direct sum of the shifted pieces of `A`. -/
  presentation_obj (n : ℤ) (U : Cᵒᵖ) :
    (presentation n).obj U ≃ₗ[R.obj.obj U] freeSections A S n U
  /-- Its restriction maps send a summand to the summand of the restricted generator. -/
  presentation_map (n : ℤ) {U V : Cᵒᵖ} (f : U ⟶ V) (i : ℤ) (s : S.sheaf.obj.obj U)
      (hs : S.HasDegree U s i) (t : S.sheaf.obj.obj V) (ht : S.HasDegree V t i)
      (hst : S.sheaf.obj.map f s = t) (x : (A.piece (n - i)).val.obj U) :
    presentation_obj n V ((presentation n).map f
        ((presentation_obj n U).symm (freeOf A S n U i s hs x))) =
      freeOf A S n V i t ht (sectionRestrict (A.piece (n - i)).val f x)
  /-- Each piece of the module is the sheafification of the presentation. -/
  piece_iso (n : ℤ) :
    module.piece n ≅ (PresheafOfModules.sheafification (𝟙 R.obj)).obj (presentation n)
  /-- The canonical homogeneous generators. -/
  generator : GradedGeneratorFamily S module
  /-- The generator of a section of degree `n` is the image of the summand `s · 1`. -/
  generator_is_basis (n : ℤ) (U : Cᵒᵖ) (s : S.sheaf.obj.obj U) (hs : S.HasDegree U s n) :
    (piece_iso n).hom.val.app U (generator.app n U s hs) =
      (CategoryTheory.toSheafify J (presentation n).presheaf).app U
        ((presentation_obj n U).symm
          (freeOf A S n U n s hs (castHom A.piece (sub_self n).symm U (A.one.eval U))))
  /-- The action of a homogeneous section of `A` on a generator. -/
  action_on_generator (n m : ℤ) (U : Cᵒᵖ) (s : S.sheaf.obj.obj U) (hs : S.HasDegree U s n)
      (b : (A.piece m).val.obj U) :
    (piece_iso (n + m)).hom.val.app U (module.smul n m U (generator.app n U s hs) b) =
      (CategoryTheory.toSheafify J (presentation (n + m)).presheaf).app U
        ((presentation_obj (n + m) U).symm
          (freeOf A S (n + m) U n s hs (castHom A.piece (by omega : m = n + m - n) U b)))
  /-- The homomorphism determined by a family of homogeneous generators. -/
  lift (N : GradedModule.{t, a, max w a} A) (g : GradedGeneratorFamily S N) :
    GradedModule.Hom module N
  /-- It sends each generator to the prescribed section. -/
  lift_generator (N : GradedModule.{t, a, max w a} A) (g : GradedGeneratorFamily S N) (n : ℤ)
      (U : Cᵒᵖ) (s : S.sheaf.obj.obj U) (hs : S.HasDegree U s n) :
    ((lift N g).app n).val.app U (generator.app n U s hs) = g.app n U s hs
  /-- Two homomorphisms agreeing on the generators are equal. -/
  hom_ext (N : GradedModule.{t, a, max w a} A) (f g : GradedModule.Hom module N)
      (h : ∀ (n : ℤ) (U : Cᵒᵖ) (s : S.sheaf.obj.obj U) (hs : S.HasDegree U s n),
        (f.app n).val.app U (generator.app n U s hs) =
          (g.app n).val.app U (generator.app n U s hs)) : f = g
  /-- When `A` is the graded algebra underlying a differential graded algebra `D`, the free
  module carries the differential for which every generator is closed. -/
  differential (D : DifferentialGradedAlgebra.{t, a} R) (h : D.toGradedAlgebra = A) :
    DifferentialGradedModule.{t, a, max w a} D
  /-- It has the same graded pieces. -/
  differential_piece (D : DifferentialGradedAlgebra.{t, a} R) (h : D.toGradedAlgebra = A)
      (n : ℤ) : (differential D h).complex.X n = module.piece n
  /-- It has the same action. -/
  differential_action (D : DifferentialGradedAlgebra.{t, a} R) (h : D.toGradedAlgebra = A)
      (n m : ℤ) (U : Cᵒᵖ) :
    HEq (((differential D h).mul n m).app U) (module.smul n m U)
  /-- Every canonical generator is closed for it. -/
  differential_generator_closed (D : DifferentialGradedAlgebra.{t, a} R)
      (h : D.toGradedAlgebra = A) (n : ℤ) (U : Cᵒᵖ) (s : S.sheaf.obj.obj U)
      (hs : S.HasDegree U s n) :
    ((differential D h).complex.d n (n + 1)).val.app U
        ((differential_piece D h n).symm ▸ generator.app n U s hs) = 0

variable (A : GradedAlgebra.{t, a} R) (S : SheafOfGradedSets.{w} J)

/-- **The free graded `A`-module on a sheaf of graded sets**, with its presentation, its
generators, its universal property and — whenever `A` is the graded algebra underlying a
differential graded algebra — its closed-generator differential. -/
@[stacks 0FSF "free_graded_mathcal_a_module_mathcal_a_mathcal_s"]
noncomputable def freeGradedModuleData : FreeGradedModuleData A S where
  module := freeGradedModule A S
  presentation := freePres A S
  presentation_obj _ _ := LinearEquiv.refl _ _
  presentation_map := by
    intro n U V f i s hs t ht hst x
    subst hst
    exact freePres_sectionRestrict_freeOf A S n f i s hs x
  piece_iso _ := Iso.refl _
  generator := freeGenerator A S
  generator_is_basis n U s hs := freeGeneratorSection_eq A S n U s hs
  action_on_generator n m U s hs b := freeActBilin_generator A S n m U s hs b (by omega)
  lift N g := liftHom A S N g
  lift_generator N g n U s hs := liftHom_generator A S N g n U s hs
  hom_ext N _ _ h := freeGradedModule_hom_ext A S N h
  differential D _ := freeDGModule S D
  differential_piece D h n := by subst h; rfl
  differential_action D h n m U := by subst h; exact HEq.rfl
  differential_generator_closed D h n U s hs := by
    subst h
    exact freeDGModule_d_freeGenerator S D n U s hs

/-- The graded module of `freeGradedModuleData A S` is `freeGradedModule A S`. -/
@[simp] theorem freeGradedModuleData_module :
    (freeGradedModuleData A S).module = freeGradedModule A S := rfl

/-- The degree-`n` presentation of `freeGradedModuleData A S` is `freePres A S n`. -/
@[simp] theorem freeGradedModuleData_presentation (n : ℤ) :
    (freeGradedModuleData A S).presentation n = freePres A S n := rfl

/-- The generators of `freeGradedModuleData A S` are the canonical generators
`freeGenerator A S`. -/
@[simp] theorem freeGradedModuleData_generator :
    (freeGradedModuleData A S).generator = freeGenerator A S := rfl

/-- The lift of a generator family provided by `freeGradedModuleData A S` is `liftHom`. -/
@[simp] theorem freeGradedModuleData_lift (N : GradedModule.{t, a, max w a} A)
    (g : GradedGeneratorFamily S N) :
    (freeGradedModuleData A S).lift N g = liftHom A S N g := rfl

/-- The differential graded module provided by `freeGradedModuleData A S` for a differential
graded algebra `D` with underlying graded algebra `A` is `freeDGModule S D`. -/
@[simp] theorem freeGradedModuleData_differential (D : DifferentialGradedAlgebra.{t, a} R)
    (h : D.toGradedAlgebra = A) :
    (freeGradedModuleData A S).differential D h = freeDGModule S D := rfl

end Bundle

end SheafOfModules
