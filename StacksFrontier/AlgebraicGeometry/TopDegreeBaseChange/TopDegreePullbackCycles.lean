module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.DerivedModelCrossing
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.MapHomologyCycles
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.RepresentativeHomology

/-!
# The cycle-class characterization of the top-degree pullback comparison

The statement of Stacks Tag 0EX3 includes, beside its data `def`
`topDirectImagePullbackIso`, a characterization of that comparison **on cycle classes**: for every
cochain complex `P` with an identification `e` of its class with `Rf'_*(F'[0])`, the pullback of
the cycle class of `P` in degree `d`, carried through the comparison and the derived-pullback
counit, is the class of its pullback.

This file states that characterization in library names, reduces it to an identity with no
cycles in it, and then **removes the quantifier over representatives**: that identity need only be
checked at one complex, and the canonical choice is the degree-`≤ d` truncation, which has no
terms above `d` at all.

The first reduction is not a reformulation for its own sake: the characterization is a
cycle-level identity through two inverted maps for which only `IsIso` is available, and the two
maps really do have no cycle-level description. What the reduction shows is that none is needed. Ordinary pullback of sheaves of modules is **right
exact**, so `h^*` applied to the projection `Z^d(P) ⟶ H^d(P)` is again a cokernel projection and
hence an epimorphism; the cycle-class equation therefore determines its right-hand factor
uniquely, and it holds exactly when that factor is the canonical comparison
`Stacks.MapHomologyCycles.mapHomology`.

## Main definitions

* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.representativeClass`: the identification of the
  homology of a representative with the cohomology of the object it represents — Stacks Tag 0BDL's
  cycle-class map, at library names.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.homologyPullbackRepresentativeComparison`: the
  derived-pullback counit on cohomology, read through a representative — Stacks Tag 0BDL's
  declaration of the same name, at library names.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.truncLERepresentative`: the identification of the
  class of the degree-`≤ a` truncation of a representative, induced by that of the representative.

## Main results

* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.topDirectImagePullbackIso_cycles_iff`: Tag 0EX3's
  cycle-class characterization of `topDirectImagePullbackIso` holds **iff** the cycle-free
  identity
  `h^*(class) ≫ topDirectImagePullbackIso ≫ counit = mapHomology h^* P d`
  holds. The remaining content of the theorem of Tag 0EX3 is that single identity.
* `TopDegreeBaseChange.representativeClass_comp_eq_mapHomology_of_quasiIso`
  and `...representativeClass_comp_eq_mapHomology_of_truncLE`: that identity holds for **every**
  representative as soon as it holds for one receiving a quasi-isomorphism, and in particular as
  soon as it holds at the truncation `τ^{≤a} P`. Both are instances of
  `Stacks.RepresentativeHomology.eq_mapHomology_of_quasiIso`, and neither uses anything about the
  comparison being characterized.

## Implementation notes

*The third declaration of Tag 0BDL needs no library counterpart.* Its `pullbackCycles` is the
`HomologicalComplex.liftCycles` of `h^*` applied to the inclusion of the cycles, which is
`Stacks.MapHomologyCycles.mapCycles` at `h^*` — the same term, with
`(ComplexShape.up ℤ).next a` written as `a + 1`. It is used here under that name rather than
duplicated.

*Everything is stated at the `Scheme.Modules` spelling and the proof is in term mode.* Mixing
`Scheme.Modules` with `SheafOfModules (structureSheafRing _)` is what this directory's other
modules record as a wall; here the statement elaborates at the `Scheme.Modules` spelling without a
transport, but `rw` and `simp only` both refuse even `Functor.map_comp` on it, reporting that
*"the target expression is not type-correct under the `implicit` transparency level"* — the two
spellings of the category of modules on `S.Y'` are not interchangeable while a rewrite motive
is being formed. A term-mode proof forms no motive, so `Functor.map_comp` and `Category.assoc`
are applied as terms and the wall does not arise. **This is a cure for the wall that needs no
transparency option.**

*The two comparisons are the generic ones specialised.* `representativeClass` and
`homologyPullbackRepresentativeComparison` are `Stacks.RepresentativeHomology`'s
`classOfRepresentative` and `comparisonOfRepresentative` at `G = h^*`; their declared return types
are unchanged, and the specialisation is `rfl`, verified by a term application. Keeping the
mathematics in a geometry-free module is what makes the reductions provable at all: the generic
statements mention one spelling of the category of modules and none of the wall below arises in
them, and the crossing happens only in argument position here.

*Right exactness is a local instance.* `RingedSpaceModuleAdjunction.modulePullback` preserves all
colimits by the adjunction; `preservesFiniteColimits_modulePullback` is a `theorem` rather than an
`instance`, and the statement of the reduction needs it at elaboration time, so it is made a local
instance rather than introduced inside the proof.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 0BDL](https://stacks.math.columbia.edu/tag/0BDL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Category
open RingedSpaceModuleAdjunction

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

universe u

open DerivedCategory

attribute [local instance] HasDerivedCategory.standard
attribute [local instance]
  RingedSpaceModuleAdjunction.preservesFiniteColimits_modulePullback

section Representative

variable {Y Z : Scheme.{u}} (g : Y ⟶ Z) (P : CochainComplex Z.Modules ℤ)

/-- **The cycle class of a representative.** For a cochain complex `P` with an identification `e`
of its class in the derived category with `K`, this is the induced identification of `H^a(P)` with
`H^a(K)`, through the two factorizations of the cohomology functor.

This is `Stacks.RepresentativeHomology.classOfRepresentative` at the category of modules on a
scheme; the geometric name is kept because it is the one used for Tag 0BDL. -/
def representativeClass {K : DerivedCategory Z.Modules}
    (e : (Qh.obj ((HomotopyCategory.quotient _ _).obj P) : DerivedCategory Z.Modules) ≅ K)
    (a : ℤ) : P.homology a ⟶ (homologyFunctor Z.Modules a).obj K :=
  Stacks.RepresentativeHomology.classOfRepresentative P e a

/-- **The derived-pullback counit on cohomology, read through a representative.** The derived
pullback of `K` is compared with the degreewise pullback of a representative `P`, and the result
with the cohomology of that pullback. This is Tag 0BDL's declaration of the same name at
library names, with the derived pullback and its comparison taken in the `StacksTag079W` forms.

This is `Stacks.RepresentativeHomology.comparisonOfRepresentative` at `G = h^*`,
`L = Lh^*` and the derived-pullback counit; the geometric name is kept because it is the
one used for Tag 0BDL. -/
def homologyPullbackRepresentativeComparison {K : DerivedCategory Z.Modules}
    (e : (Qh.obj ((HomotopyCategory.quotient _ _).obj P) : DerivedCategory Z.Modules) ≅ K)
    (a : ℤ) :
    (homologyFunctor Y.Modules a).obj
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback g.toLRSHom.toShHom).obj
          K) ⟶
      (((modulePullback g.toLRSHom.toShHom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P).homology a :=
  Stacks.RepresentativeHomology.comparisonOfRepresentative
    (modulePullback g.toLRSHom.toShHom)
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback g.toLRSHom.toShHom)
    (fun P => (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison
      g.toLRSHom.toShHom).app
      ((HomotopyCategory.quotient _ _).obj P)) P e a

end Representative

/-- **The cycle-class characterization of `topDirectImagePullbackIso` is equivalent to one
identity with no cycles in it.**

The left-hand side is the statement `topDirectImagePullbackIso_cycles` of Tag 0EX3 at library
names. The right-hand side says that the comparison,
followed by the derived-pullback counit at the representative, *is* the canonical right-exact
comparison `Stacks.MapHomologyCycles.mapHomology` of `h^*` with degree-`d` cohomology.

The two are equivalent because `h^*` is right exact, so `h^*` of the projection from the cycles
onto the homology is a cokernel projection, hence an epimorphism, and the cycle-class equation
determines what it is composed with — which is `Stacks.MapHomologyCycles.mapHomology_eq`. So the
remaining content of the theorem of Tag 0EX3 is the right-hand identity, and **no cycle-level
description of either of the two inverted maps inside `topDirectImagePullbackIso` is required**. -/
theorem topDirectImagePullbackIso_cycles_iff
    (S : Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.{u})
    (F' : S.X'.Modules) [F'.IsQuasicoherent]
    {Y'' : Scheme.{u}} (h : Y'' ⟶ S.Y')
    (P : CochainComplex S.Y'.Modules ℤ)
    (e : (Qh.obj ((HomotopyCategory.quotient _ _).obj P) :
        DerivedCategory S.Y'.Modules) ≅
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward
        S.f'.toLRSHom.toShHom).obj
        ((singleFunctor S.X'.Modules 0).obj F')) :
    ((modulePullback h.toLRSHom.toShHom).map
          (P.homologyπ (S.d : ℤ) ≫ representativeClass P e (S.d : ℤ)) ≫
        (topDirectImagePullbackIso S F' h).hom ≫
        homologyPullbackRepresentativeComparison h P e (S.d : ℤ) =
      Stacks.MapHomologyCycles.mapCycles (modulePullback h.toLRSHom.toShHom) P (S.d : ℤ) ≫
        (((modulePullback h.toLRSHom.toShHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P).homologyπ (S.d : ℤ)) ↔
    ((modulePullback h.toLRSHom.toShHom).map (representativeClass P e (S.d : ℤ)) ≫
        (topDirectImagePullbackIso S F' h).hom ≫
        homologyPullbackRepresentativeComparison h P e (S.d : ℤ) =
      Stacks.MapHomologyCycles.mapHomology
        (modulePullback h.toLRSHom.toShHom) P (S.d : ℤ)) := by
  have key : (modulePullback h.toLRSHom.toShHom).map
        (P.homologyπ (S.d : ℤ) ≫ representativeClass P e (S.d : ℤ)) ≫
      (topDirectImagePullbackIso S F' h).hom ≫
        homologyPullbackRepresentativeComparison h P e (S.d : ℤ) =
      (modulePullback h.toLRSHom.toShHom).map (P.homologyπ (S.d : ℤ)) ≫
        (modulePullback h.toLRSHom.toShHom).map (representativeClass P e (S.d : ℤ)) ≫
        (topDirectImagePullbackIso S F' h).hom ≫
          homologyPullbackRepresentativeComparison h P e (S.d : ℤ) :=
    (congrArg (· ≫ (topDirectImagePullbackIso S F' h).hom ≫
      homologyPullbackRepresentativeComparison h P e (S.d : ℤ)) (Functor.map_comp _ _ _)).trans
      (assoc _ _ _)
  exact ⟨fun hh => Stacks.MapHomologyCycles.mapHomology_eq
      (modulePullback h.toLRSHom.toShHom) P (S.d : ℤ) _ (key.symm.trans hh),
    fun hh => key.trans ((congrArg _ hh).trans
      (Stacks.MapHomologyCycles.homologyπ_comp_mapHomology
        (modulePullback h.toLRSHom.toShHom) P (S.d : ℤ)))⟩

section Reduction

variable {Y Z : Scheme.{u}} (g : Y ⟶ Z)

/-- **The cycle-free identity is insensitive to the representative.** If `ψ : P₁ ⟶ P` is a
quasi-isomorphism of representatives of the same object of the derived category — the
identification of `P₁` being the one `ψ` induces from that of `P` — then the identity
`h^*(class) ≫ γ ≫ counit = mapHomology h^*` at `P₁` gives it at `P`.

The morphism `γ` is **arbitrary**: nothing about it is used. In particular this applies with `γ`
the comparison `topDirectImagePullbackIso`, and it retires the quantifier over representatives in
`topDirectImagePullbackIso_cycles_iff`: that identity need only be checked at one convenient
complex. This is
`Stacks.RepresentativeHomology.eq_mapHomology_of_quasiIso` at `G = h^*`, `L = Lh^*` and the
derived-pullback counit, whose naturality square is the counit's own naturality. -/
theorem representativeClass_comp_eq_mapHomology_of_quasiIso
    {P₁ P : CochainComplex Z.Modules ℤ} (ψ : P₁ ⟶ P) (hψ : QuasiIso ψ)
    {K : DerivedCategory Z.Modules}
    (e : (Qh.obj ((HomotopyCategory.quotient _ _).obj P) : DerivedCategory Z.Modules) ≅ K)
    (e₁ : (Qh.obj ((HomotopyCategory.quotient _ _).obj P₁) : DerivedCategory Z.Modules) ≅ K)
    (he : e₁.hom = Qh.map ((HomotopyCategory.quotient _ _).map ψ) ≫ e.hom) (a : ℤ)
    (γ : (modulePullback g.toLRSHom.toShHom).obj ((homologyFunctor Z.Modules a).obj K) ⟶
      (homologyFunctor Y.Modules a).obj
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback g.toLRSHom.toShHom).obj
          K))
    (h₁ : (modulePullback g.toLRSHom.toShHom).map (representativeClass P₁ e₁ a) ≫ γ ≫
        homologyPullbackRepresentativeComparison g P₁ e₁ a =
      Stacks.MapHomologyCycles.mapHomology (modulePullback g.toLRSHom.toShHom) P₁ a) :
    (modulePullback g.toLRSHom.toShHom).map (representativeClass P e a) ≫ γ ≫
        homologyPullbackRepresentativeComparison g P e a =
      Stacks.MapHomologyCycles.mapHomology (modulePullback g.toLRSHom.toShHom) P a :=
  Stacks.RepresentativeHomology.eq_mapHomology_of_quasiIso
    (modulePullback g.toLRSHom.toShHom)
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback g.toLRSHom.toShHom)
    (fun P => (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison
      g.toLRSHom.toShHom).app
      ((HomotopyCategory.quotient _ _).obj P)) ψ
    ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison
      g.toLRSHom.toShHom).naturality
      ((HomotopyCategory.quotient _ _).map ψ)) e e₁ he a hψ γ h₁

/-- **The identification of the class of the degree-`≤ a` truncation.** For a complex with no
cohomology above `a` the inclusion `τ^{≤a} P ⟶ P` is a quasi-isomorphism, so an identification of
the class of `P` with `K` induces one for the truncation. -/
def truncLERepresentative (P : CochainComplex Z.Modules ℤ)
    {K : DerivedCategory Z.Modules}
    (e : (Qh.obj ((HomotopyCategory.quotient _ _).obj P) : DerivedCategory Z.Modules) ≅ K)
    (a : ℤ) [P.IsLE a] :
    (Qh.obj ((HomotopyCategory.quotient _ _).obj (P.truncLE a)) :
      DerivedCategory Z.Modules) ≅ K :=
  @asIso _ _ _ _ _ (isIso_Qh_map_quotient_map (P.ιTruncLE a) inferInstance) ≪≫ e

/-- **It suffices to check the cycle-free identity at a complex with no terms above the top
degree.** For a representative `P` with no cohomology above `a`, the identity at `P` follows from
the identity at the truncation `τ^{≤a} P`, which satisfies `CochainComplex.IsStrictlyLE a`.

That is the hypothesis under which the two remaining inputs become available: a right exact
functor commutes with the top cohomology of a strictly bounded-above complex
(`Stacks.AlgebraicGeometry.TopDegreeBaseChange.mapTopHomologyIso`), and the derived-pullback
counit is invertible on degree-`a` cohomology
(`isIso_homologyFunctor_map_derivedPullbackComparison_app`, in this namespace).
**No K-flatness is needed**: the invertibility
of the counit on the top cohomology holds for every strictly bounded-above complex. -/
theorem representativeClass_comp_eq_mapHomology_of_truncLE
    (P : CochainComplex Z.Modules ℤ) {K : DerivedCategory Z.Modules}
    (e : (Qh.obj ((HomotopyCategory.quotient _ _).obj P) : DerivedCategory Z.Modules) ≅ K)
    (a : ℤ) [P.IsLE a]
    (γ : (modulePullback g.toLRSHom.toShHom).obj ((homologyFunctor Z.Modules a).obj K) ⟶
      (homologyFunctor Y.Modules a).obj
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback g.toLRSHom.toShHom).obj
          K))
    (h₁ : (modulePullback g.toLRSHom.toShHom).map
          (representativeClass (P.truncLE a) (truncLERepresentative P e a) a) ≫ γ ≫
        homologyPullbackRepresentativeComparison g (P.truncLE a)
          (truncLERepresentative P e a) a =
      Stacks.MapHomologyCycles.mapHomology (modulePullback g.toLRSHom.toShHom)
        (P.truncLE a) a) :
    (modulePullback g.toLRSHom.toShHom).map (representativeClass P e a) ≫ γ ≫
        homologyPullbackRepresentativeComparison g P e a =
      Stacks.MapHomologyCycles.mapHomology (modulePullback g.toLRSHom.toShHom) P a :=
  representativeClass_comp_eq_mapHomology_of_quasiIso g (P.ιTruncLE a) inferInstance e
    (truncLERepresentative P e a) rfl a γ h₁

end Reduction

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
