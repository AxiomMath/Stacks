module

public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleLength
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.AlgebraTranslation
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.FiberSupportDictionary
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.Transport
public import StacksFrontier.RingTheory.Flat.CompleteDevissagePointedChain

/-!
# A scheme-theoretic complete dévissage at a point is an algebraic one

Let `f : X ⟶ S` be locally of finite type between affine schemes, let `ℱ` be a quasi-coherent
`𝒪_X`-module of finite type and let `x : X` correspond to the prime `q` of `Γ(X, ⊤)`. Writing
`R = Γ(S, ⊤)`, `B = Γ(X, ⊤)` and `N = Γ(ℱ, ⊤)`, every complete dévissage of `ℱ/X/S` *at* `x` in
the sense of Stacks 05HI translates into a complete dévissage of `N/B/R` at `q` in the sense of
Stacks 05HZ. This is the direction of item (2) of Stacks 05I0 that the source
uses; the converse, and with it the equivalence the source states, is
`Module.nonempty_completeDevissageAt_iff` in
`StacksFrontier/AlgebraicGeometry/Flatness/Devissage/Complete/SpecCompleteDevissageAt.lean`.

The translation of a single stage is the pointed dictionary: six of the eight conditions that
`Module.DevissageStageData.Pointed` records come from
`StacksFrontier/AlgebraicGeometry/Flatness/Devissage/Complete/AlgebraDictionaryAt.lean` and the two
that mention the fibre module from
`StacksFrontier/AlgebraicGeometry/Flatness/Devissage/Complete/FiberSupportDictionary.lean`. All ten
are stated for an `AlgebraicGeometry.OneStepDevissageAt`, while a stage of a chain carries its
distinguished point as an `AlgebraicGeometry.PointedDevissageStage`, which relates the two by
`HEq`; discharging those `HEq`s is what `AlgebraicGeometry.PointedDevissageStage.g_y`,
`AlgebraicGeometry.PointedDevissageStage.exists_closedPoint` and
`AlgebraicGeometry.PointedDevissageStage.exists_toPointed` do.

The stages are then assembled by `Module.PointedCompleteDevissage.ofStage` and
`Module.PointedCompleteDevissage.cons`, which match the two constructors of
`AlgebraicGeometry.PointedDevissageChain`.

## Main definitions

* `AlgebraicGeometry.PointedDevissageChain.toPointedCompleteDevissage`: **a chain of stages of a
  complete dévissage of `ℱ/X/S` with compatible distinguished points is a complete dévissage of
  `Γ(ℱ, ⊤)/Γ(X, ⊤)/Γ(S, ⊤)` over the prime of the base, pointed at the prime of `x`.**

## Main results

* `AlgebraicGeometry.PointedDevissageStage.exists_toPointed`: **the pointed datum of the
  algebraic stage attached to a pointed stage of a chain**, with its lower prime the prime of the
  stage's distinguished point and its upper prime contracting to the prime of `x`.
* `AlgebraicGeometry.subsingleton_of_isZero_tilde`: the module attached to a module over the
  functions on an affine scheme is a zero object only if the module is trivial. This is the zero
  case of the dictionary, read on `Spec`.
* `Module.nonempty_completeDevissageAt_of_nonemptyCompleteDevissageAt` and
  `Module.nonempty_completeDevissageAt_of_completeDevissageAt`: **Stacks 05I0 (2).** A complete
  dévissage of `ℱ/X/S` at `x` gives a complete dévissage of `Γ(ℱ, ⊤)/Γ(X, ⊤)/Γ(S, ⊤)` at the
  prime corresponding to `x`.

## Implementation notes

The conclusion is stated for the rings of global sections `Γ(S, ⊤)`, `Γ(X, ⊤)` and `Γ(ℱ, ⊤)`,
not for a pair of rings `A → B` with `X = Spec B`: the two are isomorphic and never equal, since
`Γ(Spec B, ⊤)` and `B` are identified by `AlgebraicGeometry.Scheme.ΓSpecIso` and by nothing
finer. A consumer that wants the statement about `A`, `B` and `N` composes
`Module.nonempty_completeDevissageAt_ofRingEquiv` once, at the end; running the recursion in the
`Γ` spelling and transporting afterwards costs nothing, whereas matching the two spellings at
every stage would cost a transport per stage.

The recursion is the structural one on `AlgebraicGeometry.PointedDevissageChain`, and it carries
the base prime `r` of `Γ(S, ⊤)` as a parameter rather than computing it from the prime of `x`.
That is why its value is a `Module.PointedCompleteDevissage` and not a
`Module.NonemptyCompleteDevissageAt`: the latter computes its base prime as `q.under R`, which
changes from stage to stage, and the identification of the two base primes is made once by
`Module.PointedCompleteDevissage.toNonemptyCompleteDevissageAt`.

Primes read off points are passed as variables together with an equation identifying them, and
their primality is passed as an explicit argument rather than as an instance: the
`Ideal.IsPrime` instance of `(X.isoSpec.hom x).asIdeal` is not found by instance synthesis, and
the prime a consumer has in hand is one it built by contraction rather than in that syntactic
form. In the recursive step the prime of the next stage is the lower prime of the pointed datum
just constructed, whose primality is a field of that datum.

The instance arguments of `Module.PointedCompleteDevissage.cons` that concern the module dévissed
by the tail are passed positionally, as in the unpointed translation: they are stated over the
lower algebra of the translated stage, which instance synthesis does not unfold to `Γ(Y, ⊤)`
because `AlgebraicGeometry.OneStepDevissage.toDevissageStage` is not reducible.

## References

* [Stacks Project, Tag 05H5](https://stacks.math.columbia.edu/tag/05H5)
* [Stacks Project, Tag 05HI](https://stacks.math.columbia.edu/tag/05HI)
* [Stacks Project, Tag 05HZ](https://stacks.math.columbia.edu/tag/05HZ)
* [Stacks Project, Tag 05I0](https://stacks.math.columbia.edu/tag/05I0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-! ### The distinguished points of a stage, read on rings -/

namespace PointedDevissageStage

variable {X S : Scheme.{u}} {f : X ⟶ S} {F : X.Modules} {s : S} {x : X}
  [LocallyOfFiniteType f] [F.IsQuasicoherent] [F.IsFiniteType]
  {stage : DevissageStage f F s}

/- `AlgebraicGeometry.PointedDevissageStage.g_y` was duplicated here. The original is in
`Flatness/Devissage/Complete/Transport.lean`, imported above; the two statements were
identical. Two exported declarations of one name in disjoint import cones break any module
that pulls both, which is what blocked the 05I0 close. -/

/-- A pointed stage has a distinguished point of its closed subscheme, lying over `x`, mapping to
the distinguished point of its smooth scheme and alone in the fibre above it. -/
public theorem exists_closedPoint (P : PointedDevissageStage f F s x stage) (hfx : f x = s) :
    ∃ z : stage.oneStep.Z, stage.oneStep.i z = x ∧ stage.oneStep.π z = P.y ∧
      stage.oneStep.π ⁻¹' {P.y} = {z} := by
  obtain ⟨oneStep, rank, alpha, gp, gps, giso⟩ := stage
  obtain ⟨atPoint, hsame, y, hsameY⟩ := P
  subst hfx
  have h1 : atPoint.toOneStepDevissage = oneStep := eq_of_heq hsame
  subst h1
  have h2 : atPoint.y = y := eq_of_heq hsameY
  subst h2
  exact ⟨atPoint.z, atPoint.i_z, atPoint.π_z, atPoint.fiber_eq_singleton⟩

/-- **The pointed datum of the algebraic stage attached to a pointed stage of a chain.**

For a stage of a complete dévissage of `ℱ/X/S` over `s` equipped with a distinguished point over
`x`, the algebraic stage `AlgebraicGeometry.OneStepDevissage.toDevissageStage` builds carries the
pointed data of Stacks 05HZ: its lower prime is the prime of the stage's distinguished point of
the smooth scheme, and its upper prime contracts along the closed immersion to the prime of `x`.

Eight of the ten fields come from the pointed dictionary for a one-step dévissage *at a point*;
what this adds is that the one-step dévissage underlying the stage is such a dévissage, which
`AlgebraicGeometry.PointedDevissageStage` records only up to `HEq`. -/
public theorem exists_toPointed [IsAffine X] [IsAffine S]
    (P : PointedDevissageStage f F s x stage) (hfx : f x = s)
    (r : Ideal Γ(S, ⊤)) [r.IsPrime] (hr : (S.isoSpec.hom s).asIdeal = r)
    (q : Ideal Γ(X, ⊤)) (hqp : q.IsPrime) (hqx : (X.isoSpec.hom x).asIdeal = q) :
    ∃ Pt : (stage.oneStep.toDevissageStage r stage.rank stage.sectionsAlpha
        (stage.fiber_bijective_sectionsAlpha r hr)).Pointed,
      letI := stage.oneStep.affine_Y
      Pt.lowerPrime = (stage.oneStep.Y.isoSpec.hom P.y).asIdeal ∧
      Pt.upperPrime.comap stage.oneStep.i.appTop.hom = q := by
  obtain ⟨oneStep, rank, alpha, gp, gps, giso⟩ := stage
  obtain ⟨atPoint, hsame, y, hsameY⟩ := P
  subst hfx
  have h1 : atPoint.toOneStepDevissage = oneStep := eq_of_heq hsame
  subst h1
  have h2 : atPoint.y = y := eq_of_heq hsameY
  subst h2
  let _ := atPoint.toOneStepDevissage.affine_Y
  let _ := atPoint.toOneStepDevissage.affine_Z
  let _ := atPoint.toOneStepDevissage.algebraSmooth
  let _ := hqp
  let _ := (atPoint.toOneStepDevissage.Y.isoSpec.hom atPoint.y).isPrime
  let _ := (atPoint.toOneStepDevissage.Z.isoSpec.hom atPoint.z).isPrime
  have hover : (atPoint.toOneStepDevissage.Y.isoSpec.hom atPoint.y).asIdeal.LiesOver r :=
    ⟨(atPoint.comap_lowerPrime_appTop _ rfl r hr).symm⟩
  refine ⟨{ lowerPrime := (atPoint.toOneStepDevissage.Y.isoSpec.hom atPoint.y).asIdeal
            lowerPrime_isPrime := (atPoint.toOneStepDevissage.Y.isoSpec.hom atPoint.y).isPrime
            lowerPrime_liesOver := hover
            residueField_purelyTranscendental :=
              atPoint.purelyTranscendental_residueField _ rfl r hr
                (atPoint.comap_lowerPrime_appTop _ rfl r hr).symm
            upperPrime := (atPoint.toOneStepDevissage.Z.isoSpec.hom atPoint.z).asIdeal
            upperPrime_isPrime := (atPoint.toOneStepDevissage.Z.isoSpec.hom atPoint.z).isPrime
            upperPrime_under := atPoint.comap_upperPrime_appTop _ _ rfl rfl
            upperPrime_unique := atPoint.upperPrime_unique _ _ rfl rfl
            lowerPrime_mem_fiberSupport :=
              atPoint.lowerPrime_mem_fiberSupport r hr _ rfl hover
            relativeDimension_eq_support :=
              atPoint.relativeDimension_eq_support r hr _ rfl hover
                (atPoint.lowerPrime_mem_fiberSupport r hr _ rfl hover) }, rfl, ?_⟩
  exact comap_asIdeal_isoSpec_hom atPoint.toOneStepDevissage.i atPoint.z x atPoint.i_z
    (atPoint.toOneStepDevissage.Z.isoSpec.hom atPoint.z).asIdeal rfl q hqx

end PointedDevissageStage

/-! ### The recursion -/

/-- **A chain of stages of a scheme-theoretic complete dévissage with compatible distinguished
points is a pointed algebraic complete dévissage.**

For `f : X ⟶ S` locally of finite type between affine schemes and `ℱ` quasi-coherent of finite
type, a chain of stages of a complete dévissage of `ℱ/X/S` over `s` together with compatible
distinguished points above `x` gives a complete dévissage of `Γ(ℱ, ⊤)/Γ(X, ⊤)/Γ(S, ⊤)` over the
prime `r` of `Γ(S, ⊤)` corresponding to `s`, pointed at the prime `q` of `Γ(X, ⊤)` corresponding
to `x`, in the sense of Stacks 05HZ.

The final stage becomes a one-stage pointed dévissage and a nonfinal stage is prepended to the
translation of the pointed dévissage of its cokernel, which is taken at the prime of the stage's
distinguished point of the smooth scheme. -/
public def PointedDevissageChain.toPointedCompleteDevissage {S : Scheme.{u}} [IsAffine S] {s : S}
    (r : Ideal Γ(S, ⊤)) [r.IsPrime] (hr : (S.isoSpec.hom s).asIdeal = r) :
    {X : Scheme.{u}} → [IsAffine X] → {f : X ⟶ S} → {F : X.Modules} →
      {hl : LocallyOfFiniteType f} → {hq : F.IsQuasicoherent} → {ht : F.IsFiniteType} →
      {x : X} → (q : Ideal Γ(X, ⊤)) → (hqp : q.IsPrime) →
      ((X.isoSpec.hom x).asIdeal = q) → (f x = s) →
      {chain : DevissageChain s X f F hl hq ht} →
      PointedDevissageChain s X f F hl hq ht x chain →
      letI := f.appTop.hom.toAlgebra
      letI : Algebra.FiniteType Γ(S, ⊤) Γ(X, ⊤) :=
        HasRingHomProperty.appTop (P := @LocallyOfFiniteType) f hl
      letI : Module.Finite Γ(X, ⊤) Γ(F, (⊤ : X.Opens)) :=
        letI := hq
        letI := ht
        Stacks.AlgebraicGeometry.CoherentFinite.finite_sections F (isAffineOpen_top X)
      letI := hqp
      Module.PointedCompleteDevissage Γ(S, ⊤) Γ(X, ⊤) Γ(F, (⊤ : X.Opens)) r q
  | X, _, f, F, hl, hq, ht, _x, q, hqp, hqx, hfx, _, .last _ stage hzero pointed =>
      letI := f.appTop.hom.toAlgebra
      letI : Algebra.FiniteType Γ(S, ⊤) Γ(X, ⊤) :=
        HasRingHomProperty.appTop (P := @LocallyOfFiniteType) f hl
      letI : Module.Finite Γ(X, ⊤) Γ(F, (⊤ : X.Opens)) :=
        letI := hq
        letI := ht
        Stacks.AlgebraicGeometry.CoherentFinite.finite_sections F (isAffineOpen_top X)
      letI := hqp
      Module.PointedCompleteDevissage.ofStage
        (stage.oneStep.toDevissageStage r stage.rank stage.sectionsAlpha
          (stage.fiber_bijective_sectionsAlpha r hr))
        (pointed.exists_toPointed hfx r hr q hqp hqx).choose
        stage.oneStep.closedAlgHom stage.oneStep.surjective_i_appTop
        stage.oneStep.finitePresentation_i_appTop stage.oneStep.closedSectionsLinearEquiv
        (stage.surjective_sectionsAlpha_of_isZero hzero)
        (pointed.exists_toPointed hfx r hr q hqp hqx).choose_spec.2
  | X, _, f, F, hl, hq, ht, _x, q, hqp, hqx, hfx, _,
      .more _ stage hqc hft _hlft _chain pointed tail =>
      letI := f.appTop.hom.toAlgebra
      letI : Algebra.FiniteType Γ(S, ⊤) Γ(X, ⊤) :=
        HasRingHomProperty.appTop (P := @LocallyOfFiniteType) f hl
      letI : Module.Finite Γ(X, ⊤) Γ(F, (⊤ : X.Opens)) :=
        letI := hq
        letI := ht
        Stacks.AlgebraicGeometry.CoherentFinite.finite_sections F (isAffineOpen_top X)
      letI := hqp
      letI := stage.oneStep.affine_Y
      letI : Module.Finite Γ(stage.oneStep.Y, ⊤) Γ(stage.coker, (⊤ : stage.oneStep.Y.Opens)) :=
        letI := hqc
        letI := hft
        Stacks.AlgebraicGeometry.CoherentFinite.finite_sections stage.coker
          (isAffineOpen_top stage.oneStep.Y)
      @Module.PointedCompleteDevissage.cons _ _ _ _ _ _ _ _ _ _ _ _ _ _
        (stage.oneStep.toDevissageStage r stage.rank stage.sectionsAlpha
          (stage.fiber_bijective_sectionsAlpha r hr))
        (pointed.exists_toPointed hfx r hr q hqp hqx).choose
        stage.oneStep.closedAlgHom stage.oneStep.surjective_i_appTop
        stage.oneStep.finitePresentation_i_appTop stage.oneStep.closedSectionsLinearEquiv
        Γ(stage.coker, (⊤ : stage.oneStep.Y.Opens)) inferInstance
        (inferInstanceAs
          (Module Γ(stage.oneStep.Y, ⊤) Γ(stage.coker, (⊤ : stage.oneStep.Y.Opens))))
        (inferInstanceAs
          (Module.Finite Γ(stage.oneStep.Y, ⊤) Γ(stage.coker, (⊤ : stage.oneStep.Y.Opens))))
        stage.cokerSectionsEquiv
        (tail.toPointedCompleteDevissage r hr
          (pointed.exists_toPointed hfx r hr q hqp hqx).choose.lowerPrime
          (pointed.exists_toPointed hfx r hr q hqp hqx).choose.lowerPrime_isPrime
          (pointed.exists_toPointed hfx r hr q hqp hqx).choose_spec.1.symm
          (pointed.g_y hfx))
        (pointed.exists_toPointed hfx r hr q hqp hqx).choose_spec.2

/-! ### The zero case, read on `Spec` -/

/-- **The module attached to a module over the functions on an affine scheme is a zero object
only if that module is trivial.** This is the zero case of the dictionary of Stacks 05I0: the
empty dévissage of `AlgebraicGeometry.CompleteDevissageAt` asks for the sheaf to be a zero object
and the empty dévissage of `Module.CompleteDevissageAt` asks for the module to be a
subsingleton. -/
public theorem subsingleton_of_isZero_tilde {R : CommRingCat.{u}} (M : ModuleCat.{u} R)
    (h : IsZero (tilde M)) : Subsingleton M := by
  have hsec := Stacks.Algebraization.subsingleton_sections_of_isZero h (⊤ : (Spec R).Opens)
  exact ⟨fun a b => (tilde.isoTop M).toLinearEquiv.injective (hsec.allEq _ _)⟩

end AlgebraicGeometry

namespace Module

/-- **Stacks Project, Tag 05I0, item (2)** for a nonempty dévissage.

Let `f : X ⟶ S` be locally of finite type between affine schemes, let `ℱ` be a quasi-coherent
`𝒪_X`-module of finite type and let `x : X` correspond to the prime `q` of `Γ(X, ⊤)`. A nonempty
complete dévissage of `ℱ/X/S` at `x` gives a complete dévissage of
`Γ(ℱ, ⊤)/Γ(X, ⊤)/Γ(S, ⊤)` at `q`.

The base prime is the prime of `Γ(S, ⊤)` corresponding to `f x`, and that it is the contraction
of `q` is `AlgebraicGeometry.comap_asIdeal_isoSpec_hom` for `f`. -/
public theorem nonempty_completeDevissageAt_of_nonemptyCompleteDevissageAt {X S : Scheme.{u}}
    [IsAffine X] [IsAffine S] {f : X ⟶ S} {F : X.Modules} {x : X}
    [hl : LocallyOfFiniteType f] [hq : F.IsQuasicoherent] [ht : F.IsFiniteType]
    (q : Ideal Γ(X, ⊤)) (hqp : q.IsPrime) (hqx : (X.isoSpec.hom x).asIdeal = q)
    (D : AlgebraicGeometry.NonemptyCompleteDevissageAt f F x) :
    letI := f.appTop.hom.toAlgebra
    letI : Algebra.FiniteType Γ(S, ⊤) Γ(X, ⊤) :=
      HasRingHomProperty.appTop (P := @LocallyOfFiniteType) f hl
    letI : Module.Finite Γ(X, ⊤) Γ(F, (⊤ : X.Opens)) :=
      Stacks.AlgebraicGeometry.CoherentFinite.finite_sections F (isAffineOpen_top X)
    letI := hqp
    Nonempty (Module.NonemptyCompleteDevissageAt Γ(S, ⊤) Γ(X, ⊤) Γ(F, (⊤ : X.Opens)) q) := by
  let _ := f.appTop.hom.toAlgebra
  let _ : Algebra.FiniteType Γ(S, ⊤) Γ(X, ⊤) :=
    HasRingHomProperty.appTop (P := @LocallyOfFiniteType) f hl
  let _ : Module.Finite Γ(X, ⊤) Γ(F, (⊤ : X.Opens)) :=
    Stacks.AlgebraicGeometry.CoherentFinite.finite_sections F (isAffineOpen_top X)
  let _ := hqp
  let _ := (S.isoSpec.hom (f x)).isPrime
  exact ⟨(D.pointed.toPointedCompleteDevissage (S.isoSpec.hom (f x)).asIdeal rfl q hqp hqx
      rfl).toNonemptyCompleteDevissageAt
    (AlgebraicGeometry.comap_asIdeal_isoSpec_hom f x (f x) rfl q hqx
      (S.isoSpec.hom (f x)).asIdeal rfl)⟩

/-- **Stacks Project, Tag 05I0, item (2).**

Let `f : X ⟶ S` be locally of finite type between affine schemes, let `ℱ` be a quasi-coherent
`𝒪_X`-module of finite type and let `x : X` correspond to the prime `q` of `Γ(X, ⊤)`. If `ℱ/X/S`
has a complete dévissage at `x` then `Γ(ℱ, ⊤)/Γ(X, ⊤)/Γ(S, ⊤)` has a complete dévissage at `q`.

Taking `X = Spec B`, `S = Spec A` and `ℱ = Ñ` recovers the statement of the source, whose `N` is
`Γ(ℱ, ⊤)`, after composing `Module.nonempty_completeDevissageAt_ofRingEquiv` with the three
comparison isomorphisms `Γ(Spec A, ⊤) ≅ A`, `Γ(Spec B, ⊤) ≅ B` and `Γ(Ñ, ⊤) ≅ N`.

The source states item (2) as an equivalence and uses only this direction; the equivalence is
`Module.nonempty_completeDevissageAt_iff` in
`StacksFrontier/AlgebraicGeometry/Flatness/Devissage/Complete/SpecCompleteDevissageAt.lean`, whose
converse half builds the scheme-theoretic dévissage out of the algebraic one on `Spec`. -/
@[stacks 05I0 "(2): a geometric complete dévissage at a point gives an algebraic one"]
public theorem nonempty_completeDevissageAt_of_completeDevissageAt {X S : Scheme.{u}}
    [IsAffine X] [IsAffine S] {f : X ⟶ S} {F : X.Modules} {x : X}
    [hl : LocallyOfFiniteType f] [hq : F.IsQuasicoherent] [ht : F.IsFiniteType]
    (q : Ideal Γ(X, ⊤)) (hqp : q.IsPrime) (hqx : (X.isoSpec.hom x).asIdeal = q)
    (D : AlgebraicGeometry.CompleteDevissageAt f F x) :
    letI := f.appTop.hom.toAlgebra
    letI : Algebra.FiniteType Γ(S, ⊤) Γ(X, ⊤) :=
      HasRingHomProperty.appTop (P := @LocallyOfFiniteType) f hl
    letI : Module.Finite Γ(X, ⊤) Γ(F, (⊤ : X.Opens)) :=
      Stacks.AlgebraicGeometry.CoherentFinite.finite_sections F (isAffineOpen_top X)
    letI := hqp
    Nonempty (Module.CompleteDevissageAt Γ(S, ⊤) Γ(X, ⊤) Γ(F, (⊤ : X.Opens)) q) := by
  let _ := f.appTop.hom.toAlgebra
  let _ : Algebra.FiniteType Γ(S, ⊤) Γ(X, ⊤) :=
    HasRingHomProperty.appTop (P := @LocallyOfFiniteType) f hl
  let _ : Module.Finite Γ(X, ⊤) Γ(F, (⊤ : X.Opens)) :=
    Stacks.AlgebraicGeometry.CoherentFinite.finite_sections F (isAffineOpen_top X)
  let _ := hqp
  cases D with
  | empty hF => exact ⟨.empty (Stacks.Algebraization.subsingleton_sections_of_isZero hF ⊤)⟩
  | nonempty data =>
      exact (nonempty_completeDevissageAt_of_nonemptyCompleteDevissageAt q hqp hqx data).elim
        fun E => ⟨.nonempty E⟩

end Module

end
