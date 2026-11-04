module

public import StacksFrontier.AlgebraicGeometry.Spaces.InjectiveQuasicoherentPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentPushforwardQcqs
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleFlatTopos

/-!
# The direct image of an injective quasi-coherent module along a flat qcqs morphism

Let `f : X ⟶ Y` be a flat, quasi-compact and quasi-separated morphism of algebraic spaces over a
scheme `S` contained in a big fppf site `B`.  **Stacks 09TK** asserts that the direct image
`f_*` carries injective objects of `QCoh(𝒪_X)` to injective objects of `QCoh(𝒪_Y)`.

The source's proof has three inputs, each of which is a result of the development:

* quasi-compactness and quasi-separatedness of `f` make `f_*` preserve quasi-coherence, which is
  Stacks 03M9, `AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePushforward_of_qcqs`; so
  `f_*` restricts to `QCoh(𝒪_X) ⥤ QCoh(𝒪_Y)`;
* the inverse image preserves quasi-coherence along an arbitrary morphism, which is Stacks 03GA,
  `AlgebraicGeometry.Space.quasicoherentPullbackFunctor`; so `f^*` restricts to
  `QCoh(𝒪_Y) ⥤ QCoh(𝒪_X)`, and the adjunction `f^* ⊣ f_*` of Stacks 03LU restricts along the two
  fully faithful inclusions;
* flatness of `f` is flatness of the induced morphism of small étale ringed topoi, which is
  Stacks 073C, `AlgebraicGeometry.Space.isFlat_iff_smallEtaleRingedToposHom_isFlat`; so `f^*` is
  exact on all modules (Stacks 04JC) and transforms injections of quasi-coherent modules into
  injections.

A functor whose left adjoint preserves monomorphisms preserves injective objects (Stacks 015Z).

## Main definitions

* `AlgebraicGeometry.Space.quasicoherentPullbackFunctorAdjunction`: the adjunction `f^* ⊣ f_*`
  of Stacks 03LU restricted to the quasi-coherent modules, for a quasi-compact quasi-separated
  morphism.

## Main results

* `AlgebraicGeometry.Space.pushforwardPreservesQuasicoherence_of_qcqs`: Stacks 03M9, as the
  predicate `AlgebraicGeometry.Space.PushforwardPreservesQuasicoherence`.
* `AlgebraicGeometry.Space.preservesMonomorphisms_quasicoherentPullbackFunctor_of_isFlat`: the
  inverse image on quasi-coherent modules along a flat morphism transforms injections into
  injections.
* `AlgebraicGeometry.Space.injective_quasicoherentPushforward_obj_of_isFlat`: **Stacks 09TK**.

## References

* [Stacks Project, Tag 09TK](https://stacks.math.columbia.edu/tag/09TK)
* [Stacks Project, Tag 03M9](https://stacks.math.columbia.edu/tag/03M9)
* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
* [Stacks Project, Tag 073C](https://stacks.math.columbia.edu/tag/073C)
* [Stacks Project, Tag 015Z](https://stacks.math.columbia.edu/tag/015Z)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- **Stacks 03M9**, as the predicate `AlgebraicGeometry.Space.PushforwardPreservesQuasicoherence`:
the direct image along a quasi-compact quasi-separated morphism of algebraic spaces carries
quasi-coherent modules to quasi-coherent modules. -/
theorem pushforwardPreservesQuasicoherence_of_qcqs (f : X ⟶ Y)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom) :
    PushforwardPreservesQuasicoherence B S hS f :=
  isQuasicoherentOnSite_modulePushforward_of_qcqs B S hS f hfqc hfqs

/-- **The adjunction `f^* ⊣ f_*` of Stacks 03LU on the quasi-coherent modules**, for a
quasi-compact quasi-separated morphism of algebraic spaces.  The adjunction between the inverse
image and the direct image of all `𝒪`-modules restricts along the two fully faithful inclusions
of the quasi-coherent modules, the restrictions being Stacks 03GA and Stacks 03M9. -/
noncomputable def quasicoherentPullbackFunctorAdjunction (f : X ⟶ Y)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom) :
    quasicoherentPullbackFunctor B S hS f ⊣
      quasicoherentPushforward B S hS f
        (pushforwardPreservesQuasicoherence_of_qcqs B S hS f hfqc hfqs) :=
  (modulePullbackAdjunction B S hS f).restrictFullyFaithful
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (ObjectProperty.liftCompιIso _ _ _).symm (ObjectProperty.liftCompιIso _ _ _).symm

/-- The inverse image on quasi-coherent modules along a flat morphism of algebraic spaces
transforms injections into injections.

Flatness of `f` is flatness of the induced morphism of small étale ringed topoi (Stacks 073C),
so `f^*` is exact on all modules (Stacks 04JC).  A monomorphism of `QCoh(𝒪_Y)` is a monomorphism
of `Mod(𝒪_Y)`, and the inclusion of `QCoh(𝒪_X)` into `Mod(𝒪_X)` is faithful, so reflects the
conclusion. -/
theorem preservesMonomorphisms_quasicoherentPullbackFunctor_of_isFlat (f : X ⟶ Y)
    (hf : IsFlat B S hS f.hom) :
    (quasicoherentPullbackFunctor B S hS f).PreservesMonomorphisms := by
  have := preservesMonomorphisms_modulePullback_of_isFlat B S hS f
    ((isFlat_iff_smallEtaleRingedToposHom_isFlat B S hS f).mp hf)
  refine ⟨fun {A C} a _ => ?_⟩
  have : Mono a.hom := mono_hom_of_mono_quasicoherentSheaves B S hS Y a
  exact (ObjectProperty.ι _).mono_of_mono_map
    (inferInstanceAs (Mono ((modulePullback B S hS f).map a.hom)))

/-- **Stacks 09TK.**  Let `f : X ⟶ Y` be a flat, quasi-compact and quasi-separated morphism of
algebraic spaces over `S`.  If `J` is an injective object of `QCoh(𝒪_X)`, then `f_*J` is an
injective object of `QCoh(𝒪_Y)`.

Since `f` is quasi-compact and quasi-separated, `f_*` preserves quasi-coherence (Stacks 03M9);
its left adjoint `f^*` transforms injections into injections because `f` is flat, so the
criterion of Stacks 015Z applies. -/
@[stacks 09TK]
theorem injective_quasicoherentPushforward_obj_of_isFlat (f : X ⟶ Y)
    (hf : IsFlat B S hS f.hom) (hfqc : IsQuasiCompact B S hS f.hom)
    (hfqs : IsQuasiSeparated B S hS f.hom)
    (J : QuasicoherentSheaves.{u, u} B S hS X.1 X.2) [Injective J] :
    Injective ((quasicoherentPushforward B S hS f
      (pushforwardPreservesQuasicoherence_of_qcqs B S hS f hfqc hfqs)).obj J) :=
  have := preservesMonomorphisms_quasicoherentPullbackFunctor_of_isFlat B S hS f hf
  have := Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (quasicoherentPullbackFunctorAdjunction B S hS f hfqc hfqs)
  Functor.injective_obj _ _

end AlgebraicGeometry.Space

end
