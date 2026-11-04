module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GlobalPresentationTransport
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentFromCoherence
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A coherent sheaf of modules on a site is of finite presentation

`StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentFromCoherence` proves that a coherent
sheaf of modules has a *finite* global presentation on each member of a family covering the
final object, and then weakens that to a global presentation in order to conclude
quasi-coherence, Stacks 03DL(8) ⟹ 03DL(6).  The finite conclusion is left on the table there
for one reason, which its implementation notes record: passing from a covering family to the
covering sieve of an arbitrary object needs the finite presentation to be stable under
restriction along an arrow of the site, the finite analogue of
`Stacks.SheafOfModules.GlobalPresentationTransport.hasGlobalPresentation_overMap`.

That analogue is proved here, and with it the implication Stacks 03DL(8) ⟹ 03DL(7): a coherent
sheaf of modules on a ringed site is of finite presentation.  No Noetherian hypothesis and no
hypothesis on the site enter; the finiteness is already in the two clauses of coherence.

## Main results

* `Stacks.SheafOfModules.FinitePresentationTransport.hasFiniteGlobalPresentation_of_functor`: a
  finite global presentation is carried by a colimit-preserving functor matching the two
  structure sheaves and carrying the module to the target one.
* `Stacks.SheafOfModules.FinitePresentationTransport.hasFiniteGlobalPresentation_overMap`: a
  finite global presentation restricts along an arrow of the site.
* `SheafOfModules.isFinitePresentationOnSite_of_isCoherentOnSite`: **Stacks 03DL(8) implies
  Stacks 03DL(7)**, a coherent sheaf of modules on a site is of finite presentation.

## Implementation notes

The transport lemma is the finite refinement of
`Stacks.SheafOfModules.GlobalPresentationTransport.hasGlobalPresentation_of_functor`: the index
types of a finite global presentation are `Fin n` and `Fin k` on the nose, so a functor carries
one to a presentation with the same two numbers and nothing has to be reindexed.  It is stated
with the target module given separately, rather than as the image of the source under a second
copy of the functor at the module universe, so that an isomorphism identifying the image with
the intended target can be folded into the comparison `ηM`; that is what the restriction lemma
needs, and it removes the appeal to invariance under isomorphism that the infinite version makes
afterwards.

`SheafOfModules.isFinitePresentationOnSite_of_isCoherentOnSite` is deliberately **not** an
instance.  `SheafOfModules.isQuasicoherentOnSite_of_isFinitePresentationOnSite` and
`SheafOfModules.isQuasicoherentOnSite_of_isCoherentOnSite` are both instances, so making this
one too would give typeclass search two routes from coherence to quasi-coherence on every site
in the library.

The module universe is forced to agree with the universe of the coefficient rings, as it is in
`SheafOfModules.exists_coversTop_hasFiniteGlobalPresentation`, which this consumes.

## References

* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace Stacks.SheafOfModules.FinitePresentationTransport

section Transport

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

/-- **A finite global presentation is carried by a functor that preserves colimits and zero
morphisms, carries the universe-lifted structure sheaf to the universe-lifted structure sheaf,
and carries the universe-lifted module to the universe lift of the intended target.**

The numbers of generators and of relations are unchanged. -/
theorem hasFiniteGlobalPresentation_of_functor
    {C' : Type u} [Category.{v} C'] {J' : GrothendieckTopology C'} {R' : Sheaf J' RingCat.{w}}
    (M : SheafOfModules.{w} R) (N : SheafOfModules.{w} R')
    {F : SheafOfModules.{max u v w} R ⥤ SheafOfModules.{max u v w} R'}
    (hF : PreservesColimitsOfSize.{max u v w, max u v w} F)
    (hF₀ : F.PreservesZeroMorphisms)
    (η₁ : F.obj (SheafOfModules.uliftForPresentation.{u, v, w, w, max u v w}
        (SheafOfModules.unit R)) ≅
      SheafOfModules.uliftForPresentation.{u, v, w, w, max u v w} (SheafOfModules.unit R'))
    (ηM : F.obj (SheafOfModules.uliftForPresentation.{u, v, w, w, max u v w} M) ≅
      SheafOfModules.uliftForPresentation.{u, v, w, w, max u v w} N) :
    M.HasFiniteGlobalPresentation → N.HasFiniteGlobalPresentation := by
  classical
  have := hF
  have := hF₀
  let _ : PreservesColimitsOfSize.{0, 0} F := preservesColimitsOfSize_shrink F
  rintro ⟨n, k, P, Q, ι, κ, hP, hQ, a, b, hab, hc⟩
  have key : ∀ {m : ℕ} {T : SheafOfModules.{max u v w} R}
      (t : Fin m → (SheafOfModules.uliftForPresentation.{u, v, w, w, max u v w}
        (SheafOfModules.unit R) ⟶ T)),
      Nonempty (IsColimit (Cofan.mk T t)) →
        Nonempty (IsColimit (Cofan.mk (F.obj T) fun i ↦ η₁.inv ≫ F.map (t i))) := by
    rintro m T t ⟨h⟩
    exact ⟨Stacks.SheafOfModules.GlobalPresentationTransport.isColimitCofanPrecompose η₁.symm _
      ((Cofan.isColimitMapCoconeEquiv F _ (Cofan.mk T t)).toFun (isColimitOfPreserves F h))⟩
  let b' : F.obj P ⟶ SheafOfModules.uliftForPresentation.{u, v, w, w, max u v w} N :=
    F.map b ≫ ηM.hom
  have hmap : F.map a ≫ F.map b = 0 := by simpa using congrArg F.map hab
  have hab' : F.map a ≫ b' = 0 := by simp [b', reassoc_of% hmap]
  let c' := CokernelCofork.ofπ b' hab'
  have hc' : IsColimit c' := by
    let d := (parallelPair a 0) ⋙ F
    let i₁ : d ≅ parallelPair (F.map a) (F.map 0) := by
      refine NatIso.ofComponents (fun j ↦ ?_) ?_
      · cases j <;> exact Iso.refl _
      rintro _ _ (_ | _ | _) <;> simp [d]
    let i₂ : parallelPair (F.map a) (F.map 0) ≅ parallelPair (F.map a) 0 :=
      parallelPairIsoMk (Iso.refl (F.obj Q)) (Iso.refl (F.obj P))
    let i := i₁ ≪≫ i₂
    exact (IsColimit.equivOfNatIsoOfIso i (F.mapCocone (CokernelCofork.ofπ b hab)) c'
      (Cocone.ext ηM (by rintro (_ | _) <;>
        simp [c', b', d, i, i₁, i₂, parallelPairIsoMk, NatIso.ofComponents_inv_app]))).toFun
      (isColimitOfPreserves F hc.some)
  exact ⟨n, k, F.obj P, F.obj Q, _, _, key ι hP, key κ hQ, F.map a, b', hab', ⟨hc'⟩⟩

end Transport

section Restriction

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

/-- **A finite global presentation restricts along an arrow of the site.**

This is the finite analogue of
`Stacks.SheafOfModules.GlobalPresentationTransport.hasGlobalPresentation_overMap`, by the same
route: restriction between two slice sites is `SheafOfModules.overMap`, which preserves
colimits. -/
theorem hasFiniteGlobalPresentation_overMap (M : SheafOfModules.{w} R) {X Y : C} (f : X ⟶ Y)
    (h : (M.over Y).HasFiniteGlobalPresentation) : (M.over X).HasFiniteGlobalPresentation := by
  have hW : ∀ W : C, HasSheafify (J.over W) AddCommGrpCat.{max u v w} ∧
      (J.over W).WEqualsLocallyBijective AddCommGrpCat.{max u v w} := fun W ↦
    ⟨GrothendieckTopology.hasSheafify_addCommGrpCat.{max u v w, v, max u v} (J.over W),
      AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{max u v w,
        max u v, v} (J.over W)⟩
  have := (hW X).1
  have := (hW X).2
  have := (hW Y).1
  have := (hW Y).2
  have hF : PreservesColimitsOfSize.{max u v w, max u v w}
      (SheafOfModules.overMap.{max u v w} R f) :=
    Stacks.SheafOfModules.overMap_preservesColimits.{u, v, max u v w, w} R f
  have hF₀ : (SheafOfModules.overMap.{max u v w} R f).PreservesZeroMorphisms := ⟨fun _ _ ↦ rfl⟩
  have hη₁ : (SheafOfModules.overMap.{max u v w} R f).obj
      (SheafOfModules.uliftForPresentation.{max u v, v, w, w, max u v w}
        (SheafOfModules.unit (R.over Y))) ≅
      SheafOfModules.uliftForPresentation.{max u v, v, w, w, max u v w}
        (SheafOfModules.unit (R.over X)) :=
    GlobalPresentationTransport.pushforwardUliftIso.{max u v, v, w, max u v w}
        (Sheaf.pushforwardOverMapIso R f).inv (SheafOfModules.unit (R.over Y)) ≪≫
      SheafOfModules.uliftForPresentationMapIso.{max u v, v, w, w, max u v w}
        (SheafOfModules.overMapUnitIso f)
  have hηM : (SheafOfModules.overMap.{max u v w} R f).obj
      (SheafOfModules.uliftForPresentation.{max u v, v, w, w, max u v w} (M.over Y)) ≅
      SheafOfModules.uliftForPresentation.{max u v, v, w, w, max u v w} (M.over X) :=
    GlobalPresentationTransport.pushforwardUliftIso.{max u v, v, w, max u v w}
        (Sheaf.pushforwardOverMapIso R f).inv (M.over Y) ≪≫
      SheafOfModules.uliftForPresentationMapIso.{max u v, v, w, w, max u v w}
        ((SheafOfModules.overFunctorMap R f).app M)
  exact hasFiniteGlobalPresentation_of_functor.{max u v, v, w} (M.over Y) (M.over X)
    (F := SheafOfModules.overMap.{max u v w} R f) hF hF₀ hη₁ hηM h

end Restriction

end Stacks.SheafOfModules.FinitePresentationTransport

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

/-- **Stacks 03DL(8) implies Stacks 03DL(7): a coherent sheaf of modules on a site is of finite
presentation.**

`SheafOfModules.exists_coversTop_hasFiniteGlobalPresentation` supplies a family covering the
final object on whose members the module has a finite global presentation; the sieve of objects
of that family covers every object, and a finite global presentation travels along each of its
arrows by
`Stacks.SheafOfModules.FinitePresentationTransport.hasFiniteGlobalPresentation_overMap`.

This is not an instance; see the implementation notes of this file. -/
@[ega "0 5.3.2" "more general"]
theorem isFinitePresentationOnSite_of_isCoherentOnSite (M : SheafOfModules.{w} R)
    (hM : IsCoherentOnSite M) : M.IsFinitePresentationOnSite := by
  classical
  have := hM
  obtain ⟨K, Z, hZ, hpres⟩ := exists_coversTop_hasFiniteGlobalPresentation M
  refine ⟨fun W => ?_⟩
  refine ⟨{g : Over W // (Sieve.ofObjects Z W) g.hom}, fun a => a.1.left, fun a => a.1.hom,
    ?_, ?_⟩
  · have hEq : Sieve.ofArrows (fun a : {g : Over W // (Sieve.ofObjects Z W) g.hom} => a.1.left)
        (fun a => a.1.hom) = Sieve.ofObjects Z W := by
      refine le_antisymm (fun X g hg => ?_) (fun X g hg => ?_)
      · rw [Sieve.mem_ofArrows_iff] at hg
        obtain ⟨a, b, rfl⟩ := hg
        exact (Sieve.ofObjects Z W).downward_closed a.2 b
      · rw [Sieve.mem_ofArrows_iff]
        exact ⟨⟨Over.mk g, hg⟩, 𝟙 X, by simp⟩
    rw [hEq]
    exact hZ W
  · intro a
    obtain ⟨k, ⟨b⟩⟩ := (Sieve.mem_ofObjects_iff Z a.1.hom).mp a.2
    exact Stacks.SheafOfModules.FinitePresentationTransport.hasFiniteGlobalPresentation_overMap
      M b (hpres k)

end SheafOfModules

end
