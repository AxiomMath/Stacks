module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitStageTriple
public import StacksFrontier.CategoryTheory.Adjunction.ConjugateSquareCoherence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackCompMate
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.PseudonaturalityClosure

/-!
# One spelling for the adjunctions of the stage bridge of [Stacks, Tag 0EXD]

The pseudococone coherence of the stage bridge — the equation `coh1` recorded in the roadmap of
`StacksFrontier/AlgebraicGeometry/Descent/FrobeniusColimitTwoGeneratorSquare.lean`, which is what
essential surjectivity in [Stacks, Tag 0EXD] is waiting on — is an equation between five
comparisons of *left* adjoints.  It can never be checked there: `SheafOfModules.pullback` is
given by a universal property through sheafification.
`CategoryTheory.natTrans_square_of_conjugate` reduces it to the mirrored equation between the
`CategoryTheory.conjugateEquiv` mates, i.e. to an equation between restrictions of scalars,
where composition is strict.

Applying that reduction needs the eight adjunctions of the square written down, and there the
development offered two spellings of one and the same adjunction: Mathlib's
`AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f`, whose right adjoint is
`SheafOfModules.pushforward f.toRingCatSheafHom`, and
`SheafOfModules.pullbackPushforwardAdjunction f.ringSheafOnOpensHom`, which is the spelling the
stage morphisms force — the coprojections `𝒪_X ⟶ colim_F 𝒪_X` and the canonical morphism
`colim_F 𝒪_Y ⟶ f_*(colim_F 𝒪_X)` are morphisms of sheaves of rings that come from no morphism
of schemes at all, so five of the eight adjunctions of the square admit only the second
spelling.  Mixing the two leaves the mirrored equation with `Scheme.Modules` adjunctions in
three of its five mates and `SheafOfModules` ones in the rest, and then no mate can be
computed: `CategoryTheory.conjugateEquiv_comp` does not rewrite across the two, because
`X.Modules` and `SheafOfModules X.ringSheafOnOpens` are definitionally equal only at default
transparency.

This file removes the choice.  The two adjunctions are *the same term*
(`AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction_eq_ringSheafOnOpensHom`, which
is `rfl`), so the uniform `SheafOfModules` spelling may be handed to the reduction directly, and
then the mirrored equation it leaves mentions **only**
`SheafOfModules.pullbackPushforwardAdjunction` and `SheafOfModules.pushforward`.  That equation is
`AlgebraicGeometry.frobeniusStageBridge_natTrans_square`'s hypothesis, and it is the whole of
what the coherence still owes.

## Main results

* `AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction_eq_ringSheafOnOpensHom`:
  **the two spellings of the pullback–pushforward adjunction of a morphism of schemes are one
  term.**  `AlgebraicGeometry.Scheme.Modules.pullback` is by definition
  `SheafOfModules.pullback` of the comorphism and
  `AlgebraicGeometry.Scheme.Hom.ringSheafOnOpensHom` is by definition that comorphism, so the
  equality is definitional; it is recorded so that a statement written in either spelling can be
  used in the other.
* `Stacks.SheafOfModules.conjugateIsoEquiv_eqToIso_pullback`: **the mate of a transport of a
  pullback of sheaves of modules along an equality of morphisms of sheaves of rings is the
  transport of the pushforward.**  This is the one of the five mates of the stage bridge that no
  structural lemma supplied; the `eqToIso` of a `congrArg` is the shape in which
  `AlgebraicGeometry.frobeniusStageExtendScalarsPullbackIso` carries the stage formula.
* `AlgebraicGeometry.frobeniusStageBridge_natTrans_square`: **the pseudococone coherence of the
  stage bridge, reduced to the mirrored equation of the restrictions of scalars**, in the
  uniform spelling.

## Implementation notes

The mirrored equation is left as a hypothesis rather than discharged, and what blocks discharging
it is *not* the spelling any more.  Each of its five mates is a composite of
`SheafOfModules.pullbackComp`, an `eqToIso` and the inverse of another
`SheafOfModules.pullbackComp`, and the mates of those three factors are respectively
`Stacks.SheafOfModules.conjugateIsoEquiv_pullbackComp`,
`Stacks.SheafOfModules.conjugateIsoEquiv_eqToIso_pullback` and
`Stacks.SheafOfModules.conjugateIsoEquiv_pullbackComp_symm`; splitting a composite into them is
`Stacks.Mates.conjugateIsoEquiv_trans`, which takes the *intermediate* adjunction as an explicit
argument.  Writing that intermediate adjunction at the concrete morphisms of this development is
what fails, and it fails on the sites rather than on the adjunctions: the target of
`SheafOfModules.pullbackComp φ ψ` is the pullback along
`φ ≫ (F.sheafPushforwardContinuous …).map ψ` read at the site `F ⋙ G`, while the stage formula
`AlgebraicGeometry.frobeniusColimitι_comp_frobeniusColimitStructureSheafHom` is stated at the site
`Opens.map f.base`.  The two are the same functor, but checking it unfolds the sheafification
machinery as far as `getColimitCocone`, whose definition the module system does not expose, so the
comparison cannot be made at a concrete site at all.  With `F` and `G` kept abstract the same
comparison is structural and succeeds, which is how Mathlib's own `SheafOfModules.pullbackComp`
states it.  So the remaining mate computations have to be done by *general* lemmas over abstract
site functors — one for the whole three-factor composite — and only instantiated at the Frobenius
morphisms afterwards.  No compiler option is involved anywhere in this, and none would help: the
obstruction is exposure, not transparency.

## References

* [Stacks Project, Tag 0EXA](https://stacks.math.columbia.edu/tag/0EXA)
* [Stacks Project, Tag 0EXB](https://stacks.math.columbia.edu/tag/0EXB)
* [Stacks Project, Tag 0EXD](https://stacks.math.columbia.edu/tag/0EXD)
* [Stacks Project, Tag 0EXE](https://stacks.math.columbia.edu/tag/0EXE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Frobenius TopologicalSpace

universe u

namespace Stacks.SheafOfModules

variable {C : Type*} [Category C] {D : Type*} [Category D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
  [Functor.IsContinuous F J K]

/-- **The mate of a transport of a pullback of sheaves of modules along an equality of morphisms
of sheaves of rings is the transport of the pushforward**, the orientation being reversed because
conjugation is contravariant.

The transport is given as an arbitrary `CategoryTheory.eqToIso`, and the equality of pullback
functors it is taken of is a hypothesis rather than `congrArg` of `h`: at a concrete site the
`congrArg` cannot be formed inside the statement, since `SheafOfModules.pullback` carries an
instance argument that instance search cannot discharge for a bound variable.  Supplying it as a
hypothesis lets the caller form it where the instances are available, which is what
`AlgebraicGeometry.frobeniusStageExtendScalarsPullbackIso` does.

This is the mate of the middle factor of that comparison, and the one of the five mates of the
stage bridge of [Stacks, Tag 0EXD] that neither Mathlib nor the rest of this development
records. -/
theorem conjugateIsoEquiv_eqToIso_pullback
    {φ ψ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R}
    [(_root_.SheafOfModules.pushforward.{u} φ).IsRightAdjoint]
    [(_root_.SheafOfModules.pushforward.{u} ψ).IsRightAdjoint]
    (h : φ = ψ)
    (hL : _root_.SheafOfModules.pullback.{u} φ = _root_.SheafOfModules.pullback.{u} ψ)
    (hR : _root_.SheafOfModules.pushforward.{u} ψ = _root_.SheafOfModules.pushforward.{u} φ) :
    conjugateIsoEquiv (_root_.SheafOfModules.pullbackPushforwardAdjunction.{u} ψ)
        (_root_.SheafOfModules.pullbackPushforwardAdjunction.{u} φ) (eqToIso hL) = eqToIso hR := by
  subst h
  exact Iso.ext (by simp [conjugateEquiv_id])

end Stacks.SheafOfModules

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (p : ℕ) [Fact p.Prime]

/-- **The two spellings of the pullback–pushforward adjunction of a morphism of schemes are one
term.**  `AlgebraicGeometry.Scheme.Modules.pullback f` is by definition
`SheafOfModules.pullback f.toRingCatSheafHom` and
`AlgebraicGeometry.Scheme.Hom.ringSheafOnOpensHom f` is by definition
`AlgebraicGeometry.Scheme.Hom.toRingCatSheafHom f`, so both sides are
`SheafOfModules.pullbackPushforwardAdjunction` of one and the same morphism of sheaves of rings
and the equality is definitional.

It is recorded because the coherence of the stage bridge of [Stacks, Tag 0EXD] needs all eight
of its adjunctions in **one** spelling, and only the `SheafOfModules` one is available for the
five of them whose morphism of sheaves of rings — a coprojection `𝒪_X ⟶ colim_F 𝒪_X`, or the
canonical `colim_F 𝒪_Y ⟶ f_*(colim_F 𝒪_X)` — comes from no morphism of schemes. -/
theorem Scheme.Modules.pullbackPushforwardAdjunction_eq_ringSheafOnOpensHom (f : X ⟶ Y) :
    Scheme.Modules.pullbackPushforwardAdjunction f =
      _root_.SheafOfModules.pullbackPushforwardAdjunction.{u} f.ringSheafOnOpensHom := rfl

/-- **The pseudococone coherence of the stage bridge of [Stacks, Tag 0EXD], reduced to the
mirrored equation of the restrictions of scalars.**

The conclusion is the coherence itself: the stage comparison
`AlgebraicGeometry.frobeniusPullbackStageIso` of `Y`, carried along the transition functor of
[Stacks, Tag 0EXE], followed by the stage bridge
`AlgebraicGeometry.frobeniusStageExtendScalarsPullbackIso` at the stage `n`, agrees with the
bridge at the stage `n + 1` followed by the commutation
`AlgebraicGeometry.frobeniusModulesPullbackIso` of Frobenius with restriction and the stage
comparison of `X`.  It says that the family
`(frobeniusStageFunctor n, frobeniusStageExtendScalarsPullbackIso n)` is a morphism of
pseudococones, which is what the cospan transform of
`CategoryTheory.Limits.CategoricalPullback.essSurj_mapCospan` is assembled from.

The hypothesis is the same square read on the *right* adjoints, each edge replaced by its
`CategoryTheory.conjugateEquiv` mate and the order of composition reversed, exactly as
`CategoryTheory.natTrans_square_of_conjugate` asks for.  Every adjunction in it is
`SheafOfModules.pullbackPushforwardAdjunction` and every functor
`SheafOfModules.pushforward`: there is no `AlgebraicGeometry.Scheme.Modules` adjunction left,
by `AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction_eq_ringSheafOnOpensHom`. On
that side composition of pushforwards is strict — `SheafOfModules.pushforwardComp` and
`SheafOfModules.pushforwardId` are identities on sections — so the hypothesis is an equation
between `CategoryTheory.eqToHom`s and identities, which is where it can be checked. -/
theorem frobeniusStageBridge_natTrans_square (f : X ⟶ Y) (hX : IsInCharacteristic X p)
    (hY : IsInCharacteristic Y p) (n : ℕ)
    (h : conjugateEquiv
            ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{u} f.ringSheafOnOpensHom).comp
              (_root_.SheafOfModules.pullbackPushforwardAdjunction.{u}
                (frobeniusStageStructureMap X p hX n)))
            ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{u}
                (frobeniusStageStructureMap Y p hY n)).comp
              (_root_.SheafOfModules.pullbackPushforwardAdjunction.{u}
                (frobeniusColimitStructureSheafHom p f hX hY)))
            (frobeniusStageExtendScalarsPullbackIso p f hX hY n).hom ≫
          Functor.whiskerLeft
            (_root_.SheafOfModules.pushforward.{u}
              (frobeniusColimitStructureSheafHom p f hX hY))
            (conjugateEquiv
              (_root_.SheafOfModules.pullbackPushforwardAdjunction.{u}
                (frobeniusStageStructureMap Y p hY n))
              ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{u}
                  (absoluteFrobenius Y p hY).ringSheafOnOpensHom).comp
                (_root_.SheafOfModules.pullbackPushforwardAdjunction.{u}
                  (frobeniusStageStructureMap Y p hY (n + 1))))
              (frobeniusPullbackStageIso Y p hY n).hom) =
        Functor.whiskerRight
            (conjugateEquiv
              (_root_.SheafOfModules.pullbackPushforwardAdjunction.{u}
                (frobeniusStageStructureMap X p hX n))
              ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{u}
                  (absoluteFrobenius X p hX).ringSheafOnOpensHom).comp
                (_root_.SheafOfModules.pullbackPushforwardAdjunction.{u}
                  (frobeniusStageStructureMap X p hX (n + 1))))
              (frobeniusPullbackStageIso X p hX n).hom)
            (_root_.SheafOfModules.pushforward.{u} f.ringSheafOnOpensHom) ≫
          (Functor.associator
              (_root_.SheafOfModules.pushforward.{u}
                (frobeniusStageStructureMap X p hX (n + 1)))
              (_root_.SheafOfModules.pushforward.{u}
                (absoluteFrobenius X p hX).ringSheafOnOpensHom)
              (_root_.SheafOfModules.pushforward.{u} f.ringSheafOnOpensHom)).hom ≫
            Functor.whiskerLeft
                (_root_.SheafOfModules.pushforward.{u}
                  (frobeniusStageStructureMap X p hX (n + 1)))
                (conjugateEquiv
                  ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{u}
                      f.ringSheafOnOpensHom).comp
                    (_root_.SheafOfModules.pullbackPushforwardAdjunction.{u}
                      (absoluteFrobenius X p hX).ringSheafOnOpensHom))
                  ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{u}
                      (absoluteFrobenius Y p hY).ringSheafOnOpensHom).comp
                    (_root_.SheafOfModules.pullbackPushforwardAdjunction.{u}
                      f.ringSheafOnOpensHom))
                  (frobeniusModulesPullbackIso f p hX hY).hom) ≫
              (Functor.associator
                  (_root_.SheafOfModules.pushforward.{u}
                    (frobeniusStageStructureMap X p hX (n + 1)))
                  (_root_.SheafOfModules.pushforward.{u} f.ringSheafOnOpensHom)
                  (_root_.SheafOfModules.pushforward.{u}
                    (absoluteFrobenius Y p hY).ringSheafOnOpensHom)).inv ≫
                Functor.whiskerRight
                    (conjugateEquiv
                      ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{u}
                          f.ringSheafOnOpensHom).comp
                        (_root_.SheafOfModules.pullbackPushforwardAdjunction.{u}
                          (frobeniusStageStructureMap X p hX (n + 1))))
                      ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{u}
                          (frobeniusStageStructureMap Y p hY (n + 1))).comp
                        (_root_.SheafOfModules.pullbackPushforwardAdjunction.{u}
                          (frobeniusColimitStructureSheafHom p f hX hY)))
                      (frobeniusStageExtendScalarsPullbackIso p f hX hY (n + 1)).hom)
                    (_root_.SheafOfModules.pushforward.{u}
                      (absoluteFrobenius Y p hY).ringSheafOnOpensHom) ≫
                  (Functor.associator
                      (_root_.SheafOfModules.pushforward.{u}
                        (frobeniusColimitStructureSheafHom p f hX hY))
                      (_root_.SheafOfModules.pushforward.{u}
                        (frobeniusStageStructureMap Y p hY (n + 1)))
                      (_root_.SheafOfModules.pushforward.{u}
                        (absoluteFrobenius Y p hY).ringSheafOnOpensHom)).hom) :
    Functor.whiskerRight (frobeniusPullbackStageIso Y p hY n).hom
        (_root_.SheafOfModules.pullback.{u}
          (frobeniusColimitStructureSheafHom p f hX hY)) ≫
        (frobeniusStageExtendScalarsPullbackIso p f hX hY n).hom =
      (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (Scheme.Modules.pullback (absoluteFrobenius Y p hY))
            (frobeniusStageExtendScalarsPullbackIso p f hX hY (n + 1)).hom ≫
          (Functor.associator _ _ _).inv ≫
            Functor.whiskerRight (frobeniusModulesPullbackIso f p hX hY).hom
                (frobeniusStageExtendScalars X p hX (n + 1)) ≫
              (Functor.associator _ _ _).hom ≫
                Functor.whiskerLeft (Scheme.Modules.pullback f)
                  (frobeniusPullbackStageIso X p hX n).hom :=
  natTrans_square_of_conjugate
    (_root_.SheafOfModules.pullbackPushforwardAdjunction.{u}
      (absoluteFrobenius Y p hY).ringSheafOnOpensHom)
    (_root_.SheafOfModules.pullbackPushforwardAdjunction.{u}
      (frobeniusStageStructureMap Y p hY (n + 1)))
    (_root_.SheafOfModules.pullbackPushforwardAdjunction.{u}
      (frobeniusStageStructureMap Y p hY n))
    (_root_.SheafOfModules.pullbackPushforwardAdjunction.{u}
      (frobeniusColimitStructureSheafHom p f hX hY))
    (_root_.SheafOfModules.pullbackPushforwardAdjunction.{u} f.ringSheafOnOpensHom)
    (_root_.SheafOfModules.pullbackPushforwardAdjunction.{u}
      (absoluteFrobenius X p hX).ringSheafOnOpensHom)
    (_root_.SheafOfModules.pullbackPushforwardAdjunction.{u}
      (frobeniusStageStructureMap X p hX (n + 1)))
    (_root_.SheafOfModules.pullbackPushforwardAdjunction.{u}
      (frobeniusStageStructureMap X p hX n))
    _ _ _ _ _ h

end AlgebraicGeometry

end
