module

public import StacksFrontier.AlgebraicGeometry.Picard.EssentiallySmall.Invertible
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentAlgebraCongr
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.SmallModel

/-!
# The sets `F_d(T)` are essentially small

Let `S` be a scheme and `𝒜` a graded `𝒪_S`-algebra (Situation 01NN), fix an integer `d`, and let
`F_d(T)` be the set of strict equivalence classes of quadruples `(d, f : T → S, L, ψ)` of
Section 01NS over a test scheme `T`. A quadruple records an invertible `𝒪_T`-module, so `F_d(T)`
lives in `Type (u + 1)` while `Mor(T, Y)` lives in `Type u`; every statement comparing the two —
the bijection of [Stacks, Tag 01NU], the `equiv` field of
`...RelativeProjQcohSheaf.DegreeRepresentation`, and the model `G` of
`...RelativeProjQcohSheaf.Representable` — therefore contains the assertion that `F_d(T)` is
**essentially small**, and that assertion was carried as a hypothesis everywhere in this
directory.

This file **proves it**, unconditionally: no affine base, no quasi-coherence of `𝒜`, no Zariski
sheaf property, and no representability.

## The argument

A quadruple is an invertible module `L` together with a map `ψ`, and `ψ` lives in a `Type u` set
once `L` is fixed: it is a family, indexed by `ℤ`, of morphisms of sheaves of modules on `T`, and
the category of sheaves of modules on a scheme is locally small
(`Stacks.SheafOfModules.locallySmall`). What is not `Type u` is the collection of possible `L`,
and that is exactly what strict equivalence quotients by: a quadruple is strictly equivalent to
any quadruple obtained by transporting it along an isomorphism of its invertible module.

So it suffices to know that the invertible modules on `T` meet a *set* of isomorphism classes,
which is [Stacks, Tag 040B]
(`Stacks.SheafOfModules.essentiallySmall_isInvertible`): there is a small family of invertible
modules such that every invertible module is isomorphic to a member. Transporting a quadruple
onto a member is `Quadruple.congrModule`, built from the functoriality of the Laurent algebra in
the invertible module (`...LaurentAlgebraCongr.laurentCongrIso`), and it is strictly equivalent to
the original one by construction. Hence the small set of pairs (member of the family, map `ψ` on
it) surjects onto `F_d(T)`'s fibre over a morphism `f : T ⟶ S`, and `F_d(T)` is the sum of those
fibres over the `Type u` set of morphisms `T ⟶ S`.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Twisting.congrModule` and
  `...RelativeProjQcohSheaf.Quadruple.congrModule`: **a quadruple transported along an
  isomorphism of its invertible module.**

## Main results

* `...RelativeProjQcohSheaf.Quadruple.strictlyEquivalent_congrModule`: a transported quadruple is
  strictly equivalent to the original one, so the transport does not move its class in `F_d(T)`.
* `...RelativeProjQcohSheaf.Quadruple.small_quotient`: **the strict equivalence classes of
  quadruples over a fixed morphism `f : T ⟶ S` form an essentially small set.**
* `...RelativeProjQcohSheaf.Fd.small`: **the sets `F_d(T)` are essentially small**, as an
  instance, which is what discharges the smallness hypothesis wherever it is carried.
* `...RelativeProjQcohSheaf.Fd.exists_representableBy_functor_of_charts` and
  `...Fd.isRepresentable_functor_of_charts`: **Tag 01NV with the smallness of the sets `F_d(T)`
  not assumed** — what is still bound is the Zariski sheaf property of `F_d`, which is the
  theorem `...RelativeProjQcohSheaf.Fd.isSheaf_functor` of a file downstream of this one, and
  what is still carried is the charts of Tag 01NU. The form of Tag 01NV binding only the charts
  is `...RelativeProjQcohSheaf.Fd.exists_representableBy_functor_of_charts'` of
  `StacksFrontier/AlgebraicGeometry/RelativeProjQcohSheaf/RepresentableOfCharts.lean`.

## Implementation notes

**Why the transport has to be built and could not be read off.** Strict equivalence of
quadruples is *defined* by an isomorphism of the Laurent algebras with prescribed degree-one
component, so producing a quadruple on a prescribed invertible module out of a given one is not
formal: the map `ψ` has to be composed with a homomorphism of sheaves of graded algebras
`⨁_n L^{⊗ n} ⟶ ⨁_n (L')^{⊗ n}`, and the multiplicativity and the unit normalisation of the
composite have to be checked. The homomorphism is
`...LaurentAlgebraCongr.laurentCongrIso`; its multiplicativity in the `mulSheaf` vocabulary that
`...RelativeProjQcohSheaf.Twisting` is stated in is `...LaurentAlgebraCongr.congrIso_mulSheaf`,
and the unit normalisation is the degree-zero value `...LaurentCongr.congrIso_zero` together with
`...RelativeProjQcohSheaf.oneHom_laurent`, both units being the identity of the structure sheaf.

The associativity steps of `Twisting.congrModule` are written in term mode: a goal mentioning the
multiplication of the Laurent algebra and the comparison of Tag 01CD at once is not type-correct
at the `implicit` transparency `rw` checks its motive at, and `rw` then reports a missing pattern
rather than the cause.

**The smallness is not an instance of the invertible-module bound by itself.** [Stacks, Tag 040B]
bounds the isomorphism classes of invertible modules; the quotient here is by strict equivalence
of *pairs* `(L, ψ)`, which is finer than isomorphism of the `L`. What makes the bound suffice is
that every isomorphism of the invertible modules is realised by a strict equivalence of
transported quadruples, which is `Quadruple.strictlyEquivalent_congrModule`.

**The smallness does not need the reduction to Tag 01NU.**
`...RelativeProjQcohSheaf.Fd.small_of_cover`, `...Fd.small_of_openImmersion_cover` and
`...Fd.small_of_baseCover` derive the smallness of the sets `F_d(T)` from the smallness of the
values of the subfunctors of the source's step (2), hence from Tag 01NU. `Fd.small` does not go
through them: it uses neither the separatedness of `F_d` nor any cover of the base nor anything
about Tag 01NU, so the smallness is independent of the charts and not merely a consequence of
them.

**What this does not do.** It does not prove [Stacks, Tag 01NU] and it does not prove [Stacks,
Tag 01NV]. A bijection `F_d(T) ≃ Mor(T, U_d)` *implies* this smallness
(`...RelativeProjQcohSheaf.Fd.small_of_representableBy`) and is not implied by it: smallness says
the classes form a set, not which scheme's points they are. In particular the `equiv` field of
`...RelativeProjQcohSheaf.DegreeRepresentation` and of
`...RelativeProjQcohSheaf.ProjDegreeRepresentation` is **not** discharged here; what is removed
from it is only the universe obstruction that accompanies residue (i).

## References

* [Stacks Project, Tag 040B](https://stacks.math.columbia.edu/tag/040B)
* [Stacks Project, Tag 01NV](https://stacks.math.columbia.edu/tag/01NV)
* [Stacks Project, Tag 01NU](https://stacks.math.columbia.edu/tag/01NU)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

open AlgebraicGeometry Stacks.RingedSpace Stacks.PullbackTensorCoherence
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentAlgebraCongr
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentCongr

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory

variable {T S : Scheme.{u}} {f : T ⟶ S}
  {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)} {d : ℤ}
  {L L' : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L']

/-! ### Transporting a quadruple along an isomorphism of its invertible module -/

/-- **The map `ψ` of a quadruple, transported along an isomorphism `e : L ≅ L'` of invertible
modules**: its degree-`i` component is the component of `ψ` followed by the comparison
`L^{⊗ i} ≅ (L')^{⊗ i}` of the `i`-th integral tensor powers.

The multiplicativity is the multiplicativity of `ψ` followed by that of the comparison
(`...LaurentAlgebraCongr.congrIso_mulSheaf`), and the unit normalisation holds because the
comparison is the identity in degree zero (`...LaurentCongr.congrIso_zero`), both Laurent
algebras having the identity of the structure sheaf as their unit
(`...RelativeProjQcohSheaf.oneHom_laurent`). -/
def Twisting.congrModule (ψ : Twisting f A d L) (e : L ≅ L') : Twisting f A d L' where
  app i := ψ.app i ≫ (congrIso e i).hom
  app_mul i j := by
    refine Eq.trans (congrArg
      (fun z => z ≫ SheafOfModules.GradedAlgebra.mulSheaf (laurent L') i j)
      (MonoidalCategory.tensorHom_comp_tensorHom (ψ.app i) (ψ.app j)
        (congrIso e i).hom (congrIso e j).hom).symm) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (congrArg (fun z => (ψ.app i ⊗ₘ ψ.app j) ≫ z)
      (congrIso_mulSheaf e i j).symm) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (congrArg (fun z => z ≫ (congrIso e (i + j)).hom) (ψ.app_mul i j)) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    exact congrArg (fun z => inv (pullbackTensorComparison
        (ringedSpaceHom f) (A.piece (i * d)) (A.piece (j * d))) ≫ z)
      (Category.assoc _ _ _)
  app_one := by
    refine Eq.trans ?_ (ψ.app_one.trans ((oneHom_laurent L).trans (oneHom_laurent L').symm))
    exact congrArg (fun z => Stacks.PullbackGradedAlgebra.pullbackOne (ringedSpaceHom f) A ≫
      (pullbackFunctor (ringedSpaceHom f)).map
        (eqToHom (congrArg A.piece (by ring : (0 : ℤ) = 0 * d))) ≫ z)
      (Category.comp_id (ψ.app 0))

/-- The components of the transported map are the components of `ψ` followed by the comparison of
the integral tensor powers. -/
@[simp] theorem Twisting.congrModule_app (ψ : Twisting f A d L) (e : L ≅ L') (i : ℤ) :
    (ψ.congrModule e).app i = ψ.app i ≫ (congrIso e i).hom := rfl

/-- **A quadruple transported along an isomorphism `e : L ≅ L'` of its invertible module**: the
quadruple over the same morphism `f : T ⟶ S` with invertible module `L'` and map
`Twisting.congrModule`.

The degree-one component of the transported map is the degree-one component of `ψ` followed by an
isomorphism, so it is still surjective. -/
def Quadruple.congrModule (P : Quadruple f A d) (e : P.L ≅ L') : Quadruple f A d where
  L := L'
  isInvertible := ‹_›
  twisting := P.twisting.congrModule e
  epi_app_one := by
    let := P.epi_app_one
    exact epi_comp _ _

/-- **A transported quadruple is strictly equivalent to the original one**, so it has the same
class in `F_d(T)`. The witness is `...LaurentAlgebraCongr.laurentCongrIso` of the isomorphism of
the invertible modules, which carries one map to the other in every degree by the definition of
the transport. -/
theorem Quadruple.strictlyEquivalent_congrModule (P : Quadruple f A d) (e : P.L ≅ L') :
    Quadruple.StrictlyEquivalent P (P.congrModule e) :=
  (Quadruple.strictlyEquivalent_iff_exists_hom P (P.congrModule e)).mpr
    ⟨laurentCongrIso e, fun _ => rfl⟩

/-! ### The smallness of the sets of classes -/

/-- **The strict equivalence classes of quadruples over a fixed morphism `f : T ⟶ S` form an
essentially small set.**

By [Stacks, Tag 040B] there is a small family of invertible `𝒪_T`-modules meeting every
isomorphism class, and for a fixed member of it the maps `ψ` form a `Type u` set, being families
of morphisms of sheaves of modules on `T` indexed by `ℤ`
(`Stacks.SheafOfModules.locallySmall`). Transporting a quadruple onto a member of the family
(`Quadruple.congrModule`) does not change its class
(`Quadruple.strictlyEquivalent_congrModule`), so those pairs surject onto the set of classes.

Nothing is assumed: neither the affineness of `S`, nor the quasi-coherence of `𝒜`, nor the
surjectivity of anything beyond what a quadruple carries. -/
theorem Quadruple.small_quotient (f : T ⟶ S)
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)) (d : ℤ) :
    Small.{u} (Quotient (Quadruple.setoid f A d)) := by
  have := Stacks.SheafOfModules.essentiallySmall_isInvertible
    T.toRingedSpace.presheaf (isSheafStruct T)
  obtain ⟨Q, hQs, hQle, hQiso⟩ := ObjectProperty.EssentiallySmall.exists_small_le.{u}
    (Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T))
  have := hQs
  refine small_of_surjective (f := fun x :
      (Σ X : Subtype Q, {ψ : @Twisting T S f A d X.1 (hQle X.1 X.2) //
        Epi (@Twisting.app T S f A d X.1 (hQle X.1 X.2) ψ 1)}) =>
      Quotient.mk (Quadruple.setoid f A d)
        { L := x.1.1, isInvertible := hQle x.1.1 x.1.2, twisting := x.2.1,
          epi_app_one := x.2.2 }) ?_
  intro q
  refine Quotient.inductionOn q fun P => ?_
  obtain ⟨L₀, hL₀, ⟨e⟩⟩ := hQiso P.L P.isInvertible
  let : Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L₀ :=
    hQle L₀ hL₀
  refine ⟨⟨⟨L₀, hL₀⟩, ⟨P.twisting.congrModule e, (P.congrModule e).epi_app_one⟩⟩, ?_⟩
  exact Quotient.sound (Quadruple.strictlyEquivalent_equivalence.symm
      (Quadruple.strictlyEquivalent_congrModule P e))

/-- **The sets `F_d(T)` of Section 01NS are essentially small.** `F_d(T)` is fibred over the
morphisms `T ⟶ S`, a `Type u` set, with fibres the strict equivalence classes over a fixed
morphism, essentially small by `Quadruple.small_quotient`.

This is an instance, so it discharges the smallness hypothesis of every statement that carries
one — in particular of `...RelativeProjQcohSheaf.Fd.smallPresheaf` and of the two statements of
Tag 01NV in `StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.SmallModel`, which carried it as
an instance argument. It is **not** the bijection of Tag 01NU: by
`...RelativeProjQcohSheaf.Fd.small_of_representableBy` a representation implies this smallness,
not conversely. -/
instance Fd.small (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace))
    (d : ℤ) (T : Scheme.{u}) : Small.{u} (Fd A d T) := by
  have : ∀ g : T ⟶ S, Small.{u} (Quotient (Quadruple.setoid g A d)) :=
    fun g => Quadruple.small_quotient g A d
  exact inferInstanceAs (Small.{u} (Σ g : T ⟶ S, Quotient (Quadruple.setoid g A d)))

/-! ### Tag 01NV with the smallness not assumed -/

variable (A) (d)

/-- **Stacks Project, Tag 01NV, conditionally, with the smallness of the sets `F_d(T)`
discharged.** The functor `F_d` of Section 01NS is representable by a scheme over `S`: there are
a scheme `Y`, a morphism `p : Y ⟶ S` and a representation of `F_d` by `Y` under which the
morphism `T ⟶ Y` representing a class `ξ ∈ F_d(T)`, composed with `p`, is the morphism `T ⟶ S`
recorded by `ξ`.

This is `...RelativeProjQcohSheaf.Fd.exists_representableBy_functor_of_isSheaf` with its
instance argument supplied by `Fd.small`. What remains **bound** is the Zariski sheaf property of
`F_d` — the source's step (1), which is itself a theorem,
`...RelativeProjQcohSheaf.Fd.isSheaf_functor`, but one stated in a file downstream of this one,
so the binder cannot be dropped here; the form of Tag 01NV that drops it is
`...RelativeProjQcohSheaf.Fd.exists_representableBy_functor_of_charts'` of
`StacksFrontier/AlgebraicGeometry/RelativeProjQcohSheaf/RepresentableOfCharts.lean` — and the
charts `c`, `hc`, `hcover`, that is the source's steps (2) and (3), namely
[Stacks, Tag 01NU] in the form the charts want. Tag 01NU itself is proved over an affine base
(`...AffineQuadrupleBijection.Quadruple.fdEquiv`), and for Situation 01NN and `d ≥ 1` it **is**
assembled into such a family, in
`StacksFrontier/AlgebraicGeometry/RelativeProjQcohSheaf/AffineOpenCharts.lean`
(`...RelativeProjQcohSheaf.Fd.affineOpenChart`, `...Fd.isOpenImmersion_affineOpenChart`,
`...Fd.isLocallySurjective_affineOpenCharts`), where the form of the tag that binds nothing at
all, `...Fd.isRepresentable_functor_of_pos`, is stated. The binders stay here because this
statement is more general than the tag: an arbitrary graded algebra and an arbitrary integer
`d`. -/
-- [Stacks, Tag 01NV] is registered unconditionally on
-- AffineOpenCharts.Fd.isRepresentable_functor_of_pos; this statement is the conditional form and
-- carries its hypotheses, so it does not claim the tag.
theorem Fd.exists_representableBy_functor_of_charts
    (hsheaf : Presheaf.IsSheaf Scheme.zariskiTopology.{u} (Fd.functor A d))
    {ι : Type u} {X : ι → Scheme.{u}}
    (c : (i : ι) → yoneda.obj (X i) ⟶ Fd.smallPresheaf A d)
    (hc : ∀ i, IsOpenImmersion.presheaf (c i))
    (hcover : Presheaf.IsLocallySurjective Scheme.zariskiTopology (Sigma.desc c)) :
    ∃ (Y : Scheme.{u}) (p : Y ⟶ S) (e : (Fd.functor A d).RepresentableBy Y),
      ∀ (T : Scheme.{u}) (ξ : Fd A d T), e.homEquiv.symm ξ ≫ p = ξ.1 :=
  Fd.exists_representableBy_functor_of_isSheaf A d hsheaf c hc hcover

/-- **Stacks Project, Tag 01NV, conditionally, in the bare form, with the smallness of the sets
`F_d(T)` discharged.** See `Fd.exists_representableBy_functor_of_charts` for what is carried and
what is proved. -/
-- Beyond what this declaration proves, recorded here rather than in the attribute:
--   Same accounting: the smallness of the sets F_d(T) is NO LONGER ASSUMED, being the theorem
--   Fd.small of this file; still BOUND is the Zariski sheaf property of F_d (step (1)), which is
--   the THEOREM QuadrupleGluesProof.Fd.isSheaf_functor but is stated downstream of this file, so
--   see RepresentableOfCharts.Fd.isRepresentable_functor_of_charts' for the form that drops the
--   binder; still CARRIED here are the charts c/hc/hcover presenting Tag 01NU which is itself
--   proved over an affine base as AffineQuadrupleBijection.Quadruple.fdEquiv, and IS assembled
--   into those charts in AffineOpenCharts for Situation 01NN with 0 < d, whence
--   AffineOpenCharts.Fd.isRepresentable_functor_of_pos binds nothing; the binders stay here
--   because this statement is more general than the tag
theorem Fd.isRepresentable_functor_of_charts
    (hsheaf : Presheaf.IsSheaf Scheme.zariskiTopology.{u} (Fd.functor A d))
    {ι : Type u} {X : ι → Scheme.{u}}
    (c : (i : ι) → yoneda.obj (X i) ⟶ Fd.smallPresheaf A d)
    (hc : ∀ i, IsOpenImmersion.presheaf (c i))
    (hcover : Presheaf.IsLocallySurjective Scheme.zariskiTopology (Sigma.desc c)) :
    (Fd.functor A d).IsRepresentable :=
  Fd.isRepresentable_functor_of_isSheaf A d hsheaf c hc hcover

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

end
