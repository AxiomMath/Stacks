module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.CohomologyPresheafRestriction
public import Mathlib.CategoryTheory.Sites.LocallyInjective

/-!
# A higher direct image vanishes as soon as its cohomology presheaf is locally zero

Let `u : 𝒟 ⥤ 𝒞` be a continuous functor between sites and `f_* = u^s` the induced direct image of
abelian sheaves. By [Stacks, Tag 072W] the sheaf `R^p f_* F` is the *sheafification* of the
cohomology presheaf `V ↦ H^p(u V, F)`, so `R^p f_* F = 0` holds as soon as that presheaf
sheafifies to zero — and a presheaf of abelian groups sheafifies to zero exactly when each of its
sections dies on a covering sieve.

This subsumes the input used by `isZero_rightDerived_pushforward_of_cohomologyPresheafIso`, which
asks for an *isomorphism* of cohomology presheaves with one coming from the target site: such an
isomorphism forces the sheafification to vanish ([Stacks, Tag 01FW]), while nothing forces the
converse. The difference matters for the derived clause of [Stacks, Tag 0DCU]: with the
isomorphism as the input, every step of the Stacks chain for 0DCU (7b) has to be natural in the
object `Z` of the big site over `Y`, which is what forces Leray's theorem, the comparison map
`Stacks.Cohomology.BaseChange.abelianBaseChange` and the sheaf `π_Y^{-1}(g_* J)` into the
argument. With the sheafification vanishing as the input none of those occur, and with its
per-section refinement the hypothesis quantifies over one object and one section at a time.

## Main results

In the namespace `Stacks.Cohomology.SheafifiedHigherDirectImage`:

* `isZero_presheafToSheaf_of_locallyZero`: a presheaf of abelian groups all of whose sections die
  on a covering sieve has zero sheafification.
* `isZero_rightDerived_pushforward_of_isZero_sheafify`: `R^p f_* F = 0` as soon as the cohomology
  presheaf of `F` for `u` sheafifies to zero. No positivity of `p` is needed.
* `isZero_sheafify_cohomologyPresheaf_of_cohomologyPresheafIso`: that hypothesis is implied by the
  isomorphism hypothesis of `isZero_rightDerived_pushforward_of_cohomologyPresheafIso`, so the new
  criterion subsumes the old one.
* `isZero_rightDerived_pushforward_of_locallyZero`: the same vanishing with the hypothesis stated
  on sections.

In the namespace `Stacks.Topology.LocallyQuasiCompactZariskiSituation`:

* `isIso_properDerivedImageComparison_of_isZero_sheafifyCohomologyPresheaf`: the derived clause of
  [Stacks, Tag 0DCU] for a proper map, with its remaining input reduced to the vanishing of one
  sheafification.
* `isIso_properDerivedImageComparison_of_locallyZero_cohomologyPresheaf`: the same with that input
  stated on sections.

## Implementation notes

That a presheaf with locally vanishing sections sheafifies to zero is proved through the
sheafification adjunction rather than through `GrothendieckTopology.W`: the instance identifying
`J.W` with local bijectivity is available only when the coefficient category's carrier types sit
in the universe `max u v` of the site, and the big Zariski site over `Y` carries coefficients in
`AddCommGrpCat.{max (u+1) v}` while its own `max` is `u+1`. What *is* available with no extra
hypothesis is `HasSheafCompose (forget AddCommGrpCat)`, and that is enough: it makes the presheaf
underlying a sheaf separated, so a morphism to a sheaf out of a locally zero presheaf vanishes,
and the adjunction turns that into `𝟙 = 0` on the sheafification.

## References

* [Stacks Project, Tag 0DCU](https://stacks.math.columbia.edu/tag/0DCU)
* [Stacks Project, Tag 072W](https://stacks.math.columbia.edu/tag/072W)
* [Stacks Project, Tag 01FW](https://stacks.math.columbia.edu/tag/01FW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace Stacks.Cohomology.SheafifiedHigherDirectImage

universe t v₁ u₁ v₂ u₂

section LocallyZero

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{t}] [J.HasSheafCompose (forget AddCommGrpCat.{t})]

/-- **A presheaf of abelian groups whose sections die locally has zero sheafification.** If for
every object `U` and every section `x` over `U` the sieve of morphisms along which `x` restricts
to zero is covering, then the sheafification of the presheaf is a zero object.

The proof does not go through `GrothendieckTopology.W`; see the implementation notes. A morphism
`φ` from the presheaf to the presheaf underlying a sheaf is zero, because `φ` applied to a section
restricts to zero on a covering sieve and the target is separated; the sheafification adjunction
then turns the vanishing of the unit into `𝟙 = 0`. -/
theorem isZero_presheafToSheaf_of_locallyZero (P : Cᵒᵖ ⥤ AddCommGrpCat.{t})
    (h : ∀ (U : C) (x : ToType (P.obj (op U))),
      Presheaf.equalizerSieve (F := P) (X := op U) x 0 ∈ J U) :
    IsZero ((presheafToSheaf J AddCommGrpCat.{t}).obj P) := by
  have key : ∀ (T : Sheaf J AddCommGrpCat.{t}) (φ : P ⟶ T.obj), φ = 0 := by
    intro T φ
    ext U x
    refine T.isSeparated _ _ (h U.unop x) _ _ ?_
    intro V g hg
    have hg' : P.map g.op x = P.map g.op (0 : ToType (P.obj U)) := hg
    rw [map_zero] at hg'
    rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply, hg']
    simp
  refine (IsZero.iff_id_eq_zero _).mpr ?_
  refine ((sheafificationAdjunction J AddCommGrpCat.{t}).homEquiv P _).injective ?_
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  simpa using key _ (toSheafify J P)

omit [HasSheafify J AddCommGrpCat.{t}] [J.HasSheafCompose (forget AddCommGrpCat.{t})] in
/-- **Local vanishing transports along an isomorphism of presheaves.** If every section of `Q`
dies on a covering sieve and `P ≅ Q`, then every section of `P` does. The inverse of the
isomorphism carries the witness back, so no injectivity of its components is needed. -/
theorem equalizerSieve_mem_of_presheafIso {P Q : Cᵒᵖ ⥤ AddCommGrpCat.{t}} (e : P ≅ Q)
    (h : ∀ (U : C) (y : ToType (Q.obj (op U))),
      Presheaf.equalizerSieve (F := Q) (X := op U) y 0 ∈ J U) (U : C)
    (x : ToType (P.obj (op U))) :
    Presheaf.equalizerSieve (F := P) (X := op U) x 0 ∈ J U := by
  refine J.superset_covering ?_ (h U (e.hom.app (op U) x))
  intro V g hg
  have hg' : Q.map g.op (e.hom.app (op U) x) = Q.map g.op (0 : ToType (Q.obj (op U))) := hg
  rw [map_zero] at hg'
  change P.map g.op x = P.map g.op (0 : ToType (P.obj (op U)))
  rw [map_zero]
  calc P.map g.op x
      = P.map g.op (e.inv.app (op U) (e.hom.app (op U) x)) := by simp
    _ = e.inv.app (op V) (Q.map g.op (e.hom.app (op U) x)) :=
        (NatTrans.naturality_apply e.inv g.op _).symm
    _ = 0 := by rw [hg', map_zero]

end LocallyZero

section Pushforward

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology D} {K : GrothendieckTopology C}
  (A : Type*) [Category* A] [Abelian A] [HasSheafify J A] [HasSheafify K A]
  (u : D ⥤ C) [u.IsContinuous J K] [EnoughInjectives (Sheaf K A)]

/-- **`R^p f_* F` vanishes as soon as its cohomology presheaf sheafifies to zero.** This is
[Stacks, Tag 072W] read as a vanishing criterion: `R^p f_* F` *is* the sheafification of the
presheaf `V ↦ H^p(u V, F)`.

Unlike `isZero_rightDerived_pushforward_of_cohomologyPresheafIso`, this needs neither `0 < p` nor
a sheaf on the target site whose cohomology presheaf matches. -/
theorem isZero_rightDerived_pushforward_of_isZero_sheafify (p : ℕ) (F : Sheaf K A)
    (h : IsZero ((presheafToSheaf J A).obj
      (((pushforwardCohomologyPresheaf (K := K) A u).rightDerived p).obj F))) :
    IsZero (((u.sheafPushforwardContinuous A J K).rightDerived p).obj F) :=
  IsZero.of_iso h ((rightDerivedPushforwardIso A u p).app F)

variable [EnoughInjectives (Sheaf J A)]

omit [u.IsContinuous J K] in
/-- **The sheafification hypothesis is implied by the isomorphism hypothesis.** If the `p`-th
cohomology presheaf of `F` for `u` is isomorphic to the `p`-th cohomology presheaf of a sheaf `G`
on the target site, then it sheafifies to zero, because a higher cohomology presheaf always does
([Stacks, Tag 01FW]).

So `isZero_rightDerived_pushforward_of_isZero_sheafify` subsumes
`isZero_rightDerived_pushforward_of_cohomologyPresheafIso`: anything the isomorphism input proves,
the sheafification input proves. -/
theorem isZero_sheafify_cohomologyPresheaf_of_cohomologyPresheafIso (p : ℕ) (hp : 0 < p)
    (F : Sheaf K A) (G : Sheaf J A)
    (e : ((pushforwardCohomologyPresheaf (K := K) A u).rightDerived p).obj F ≅
      ((sheafToPresheaf J A).rightDerived p).obj G) :
    IsZero ((presheafToSheaf J A).obj
      (((pushforwardCohomologyPresheaf (K := K) A u).rightDerived p).obj F)) :=
  IsZero.of_iso (isZero_sheafify_rightDerived_sheafToPresheaf (A := A) p hp G)
    ((presheafToSheaf J A).mapIso e)

end Pushforward

section PushforwardSections

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology D} {K : GrothendieckTopology C}
  (u : D ⥤ C) [u.IsContinuous J K]
  [HasSheafify J AddCommGrpCat.{t}] [HasSheafify K AddCommGrpCat.{t}]
  [J.HasSheafCompose (forget AddCommGrpCat.{t})]
  [EnoughInjectives (Sheaf K AddCommGrpCat.{t})]

/-- **`R^p f_* F = 0` from a per-section local vanishing.** The higher direct image of `F` along a
continuous functor vanishes in degree `p` as soon as every class in `H^p(u V, F)`, for every
object `V` of the target site, is killed by restriction along the members of some covering sieve
of `V`.

This is the form in which the vanishing of a higher direct image is reachable by a *pointwise*
argument: the hypothesis speaks of one object and one section at a time, so nothing has to be
natural in `V`. -/
theorem isZero_rightDerived_pushforward_of_locallyZero (p : ℕ)
    (F : Sheaf K AddCommGrpCat.{t})
    (h : ∀ (V : D) (ξ : ToType ((((pushforwardCohomologyPresheaf (K := K)
        AddCommGrpCat.{t} u).rightDerived p).obj F).obj (op V))),
      Presheaf.equalizerSieve (X := op V) ξ 0 ∈ J V) :
    IsZero (((u.sheafPushforwardContinuous AddCommGrpCat.{t} J K).rightDerived p).obj F) :=
  isZero_rightDerived_pushforward_of_isZero_sheafify AddCommGrpCat.{t} u p F
    (isZero_presheafToSheaf_of_locallyZero J _ h)

end PushforwardSections

end Stacks.Cohomology.SheafifiedHigherDirectImage

namespace Stacks.Topology.LocallyQuasiCompactZariskiSituation

universe u w v

open Stacks.Cohomology.SheafifiedHigherDirectImage

attribute [local instance] HasDerivedCategory.standard

-- See the note at the head of `AcyclicityReduction.lean`: the cheap instance for
-- `HasPointwiseRightDerivedFunctor` on `K⁺` has to be given precedence, or synthesis tries to
-- prove termwise injectivity of an unknown complex and times out.
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {S₀ : Set LocallyQuasiCompactHausdorff.{u}} {Bound : Cardinal.{u} → Cardinal.{u}}
  (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) {X Y : S.category} (f : X ⟶ Y)
  [HasSheafify (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify (Opens.grothendieckTopology Y.obj) AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify (S.zariskiTopology.over Y) AddCommGrpCat.{max (u + 1) v}]
  [EnoughInjectives (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v})]
  [EnoughInjectives (Sheaf (Opens.grothendieckTopology Y.obj) AddCommGrpCat.{max (u + 1) v})]
  [EnoughInjectives (Sheaf (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v})]

/-- **Stacks 0DCU, the derived clause, reduced to the vanishing of one sheafification.** For a
proper map `f : X ⟶ Y` the derived Zariski base-change map is invertible as soon as, for every
injective abelian sheaf `J` on the small Zariski site of `X` and every `p > 0`, the presheaf
`W ↦ H^p_{LC_Zar/X}(W ×_Y X, π_X^{-1} J)` on the big Zariski site over `Y` has zero
sheafification.

This is the weakest of the three inputs the library now has for this clause, and it subsumes the
isomorphism input of
`isIso_properDerivedImageComparison_of_restrictedCohomologyPresheafIso_pushforward`: by
`isZero_sheafify_cohomologyPresheaf_of_cohomologyPresheafIso` an isomorphism with a cohomology
presheaf of the big site over `Y` forces the sheafification to vanish, while nothing forces the
converse. In particular the sheaf `π_Y^{-1}(g_* J)`, Leray's theorem for `f' : Z ×_Y X ⟶ Z` and
the comparison map `Stacks.Cohomology.BaseChange.abelianBaseChange` all leave the critical path:
by [Stacks, Tag 072W] the hypothesis *is* the vanishing `R^p f_{Zar,*}(π_X^{-1} J) = 0`, with no
comparison map to construct and no naturality in `W` to check. -/
theorem isIso_properDerivedImageComparison_of_isZero_sheafifyCohomologyPresheaf
    (hf : StacksDraft.Topology.IsProperMap.{u, u, u}
      (((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f) : X.obj → Y.obj))
    (hsh : ∀ J : Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v},
      Injective J → ∀ p : ℕ, 0 < p →
        IsZero ((presheafToSheaf (S.zariskiTopology.over Y)
          AddCommGrpCat.{max (u + 1) v}).obj ((Over.pullback f).op ⋙
            ((sheafToPresheaf (S.zariskiTopology.over X)
                AddCommGrpCat.{max (u + 1) v}).rightDerived p).obj
              ((S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X).obj J)))) :
    IsIso (properDerivedImageComparison.{u, w, v} S f) := by
  refine isIso_properDerivedImageComparison_of_isZero_rightDerivedPlus.{u, w, v} S f hf
    fun J hJ i hi => ?_
  obtain ⟨p, hp⟩ : ∃ p : ℕ, i = (p : ℤ) := ⟨i.toNat, (Int.toNat_of_nonneg hi.le).symm⟩
  have hp0 : 0 < p := by omega
  rw [Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff _ hp]
  refine isZero_rightDerived_pushforward_of_isZero_sheafify AddCommGrpCat.{max (u + 1) v}
    (Over.pullback f) p _ (IsZero.of_iso (hsh J hJ p hp0) ?_)
  exact (presheafToSheaf (S.zariskiTopology.over Y) AddCommGrpCat.{max (u + 1) v}).mapIso
    ((pushforwardCohomologyPresheafRestrictionIso AddCommGrpCat.{max (u + 1) v}
      (Over.pullback f) p).app _)

/-- **Stacks 0DCU, the derived clause, reduced to a local vanishing.** For a proper map
`f : X ⟶ Y` the derived Zariski base-change map is invertible as soon as, for every injective
abelian sheaf `J` on the small Zariski site of `X`, every `p > 0`, every object `W` of the big
Zariski site over `Y` and every class
`ξ ∈ H^p_{LC_Zar/X}(W ×_Y X, π_X^{-1} J)`, there is a covering sieve of `W` all of whose members
kill `ξ` by restriction.

This is `isIso_properDerivedImageComparison_of_isZero_sheafifyCohomologyPresheaf` with the
sheafification hypothesis traded for the per-section criterion
`isZero_presheafToSheaf_of_locallyZero`, which is the form a pointwise argument produces: the
hypothesis speaks of one object `W` and one class `ξ` at a time, so no step of it has to be
natural in `W`. -/
theorem isIso_properDerivedImageComparison_of_locallyZero_cohomologyPresheaf
    (hf : StacksDraft.Topology.IsProperMap.{u, u, u}
      (((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f) : X.obj → Y.obj))
    (hloc : ∀ J : Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v},
      Injective J → ∀ p : ℕ, 0 < p → ∀ (W : Over Y)
        (ξ : ToType ((((Over.pullback f).op ⋙
            ((sheafToPresheaf (S.zariskiTopology.over X)
                AddCommGrpCat.{max (u + 1) v}).rightDerived p).obj
              ((S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X).obj J))).obj (op W))),
          Presheaf.equalizerSieve (X := op W) ξ 0 ∈ (S.zariskiTopology.over Y) W) :
    IsIso (properDerivedImageComparison.{u, w, v} S f) :=
  isIso_properDerivedImageComparison_of_isZero_sheafifyCohomologyPresheaf.{u, w, v} S f hf
    fun J hJ p hp => isZero_presheafToSheaf_of_locallyZero (S.zariskiTopology.over Y) _
      (hloc J hJ p hp)

end Stacks.Topology.LocallyQuasiCompactZariskiSituation

end
