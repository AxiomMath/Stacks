module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.ModuleAlgebraData
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.AdicAlgebraSheafClause
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.AdicFiniteAlgebraizationPackaging
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FiniteAlgebraization

/-!
# Grothendieck existence for finite algebras, and Stacks 09ZT, 0A42 and 0899

Let `A` be a Noetherian ring complete with respect to an ideal `I` and let `f : X ⟶ Spec A` be
separated, locally of finite type and quasi-compact. This file proves Grothendieck's existence
theorem for finite sheaves of algebras, `AlgebraicGeometry.AdicFiniteAlgebraAlgebraization A I f`,
and deduces [Stacks, Tag 09ZT], [Stacks, Tag 0A42] and [Stacks, Tag 0899] at the hypotheses of the
source.

## Main results

* `AlgebraicGeometry.adicFiniteAlgebraAlgebraization_holds`: a cartesian system of finite
  quasi-coherent algebra sheaves on the adic thickenings whose closed member has proper relative
  spectrum is the pullback of a finite quasi-coherent algebra sheaf on `X` with proper relative
  spectrum.
* `AlgebraicGeometry.adicFiniteAlgebraization_holds`: the same statement for finite schemes over
  the adic thickenings, in the form `AlgebraicGeometry.AdicFiniteAlgebraization`.
* `AlgebraicGeometry.exists_finite_algebraization_of_adicFiniteSystem_holds`: a cartesian system
  of finite schemes over the adic thickenings of `X`, proper over `Spec (A / I)` at its first
  member, is the system of base changes of a scheme finite over `X` and proper over `Spec A`.
* `AlgebraicGeometry.existsUnique_algebraization_adicBaseChangeMap_holds`: a compatible system of
  morphisms between the adic thickenings of a proper `X` and a separated `Y` of finite type comes
  from a unique morphism `X ⟶ Y` over `Spec A`.
* `AlgebraicGeometry.exists_closedImmersion_algebraization_of_isPullback_holds`: a cartesian
  system over the adic thickenings of `X` whose first member is a closed immersion proper over
  `Spec (A / I)` comes from a closed immersion into `X` proper over `Spec A`.

## References

* [Stacks Project, Tag 0899](https://stacks.math.columbia.edu/tag/0899)
* [Stacks Project, Tag 088E](https://stacks.math.columbia.edu/tag/088E)
* [Stacks Project, Tag 088F](https://stacks.math.columbia.edu/tag/088F)
* [Stacks Project, Tag 09ZT](https://stacks.math.columbia.edu/tag/09ZT)
* [Stacks Project, Tag 0A42](https://stacks.math.columbia.edu/tag/0A42)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-! ### Grothendieck existence for finite sheaves of algebras -/

/-- **Grothendieck's existence theorem for finite sheaves of algebras.** For `A` Noetherian and
complete along `I` and `f : X ⟶ Spec A` separated, locally of finite type and quasi-compact, a
cartesian system of finite quasi-coherent algebra sheaves on the adic thickenings whose closed
member has proper relative spectrum is the pullback of a finite quasi-coherent algebra sheaf on `X`
with proper relative spectrum. -/
public theorem adicFiniteAlgebraAlgebraization_holds (A : Type u) [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    AdicFiniteAlgebraAlgebraization A I f :=
  adicFiniteAlgebraAlgebraization_of_hdata A I f
    fun hpullback B hqc hBtrans hMcoh hM0 P e =>
      exists_moduleAlgebraData_algebraPullback_of_adicAlgebraModuleSystem A I f hpullback B hqc
        hBtrans hMcoh hM0 P e (isEquivalence_adicThickeningCompletionFunctor A I f)

/-- **Algebraization of finite adic systems, in the form
`AlgebraicGeometry.AdicFiniteAlgebraization`.** For `A` Noetherian and complete along `I`, and
`fP : P ⟶ Spec A` separated, locally of finite type and quasi-compact, a system of finite schemes
over the adic base changes of `P`, cartesian over the transition maps and proper over
`Spec (A / I)` at its first member, is the system of adic base changes of a scheme over `P` proper
over `Spec A`. -/
public theorem adicFiniteAlgebraization_holds (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) [IsAdicComplete I A] :
    AdicFiniteAlgebraization A I :=
  adicFiniteAlgebraization_of_adicFiniteAlgebraAlgebraization_of_qcSeparatedFiniteType A I
    fun fP => adicFiniteAlgebraAlgebraization_holds A I fP

/-! ### Stacks 09ZT -/

/-- **Algebraization of a cartesian system of finite schemes over the adic thickenings.** Let `A`
be a Noetherian ring complete with respect to an ideal `I`, write `S = Spec A` and
`Sₙ = Spec (A / Iⁿ)`, and let `f : X ⟶ S` be separated of finite type; put `Xₙ = X ×_S Sₙ`. Let
`(Yₙ)` be a system of schemes over the `Xₙ` whose squares over the transitions `Xₙ ⟶ Xₙ₊₁` are
cartesian, with every `Yₙ ⟶ Xₙ` finite and `Y₀ ⟶ S₀` proper. Then there is a finite morphism
`a : Z ⟶ X` which is proper over `S` and maps `kₙ : Yₙ ⟶ Z` over `X` exhibiting every `Yₙ` as the
fibre product `Z ×_S Sₙ`. -/
@[stacks 09ZT "at the source's hypotheses and with no further input: A Noetherian and I-adically \
complete, f : X -> Spec A separated of finite type (IsSeparated, LocallyOfFiniteType and \
QuasiCompact), a system (Y n) of schemes over the adic thickenings with cartesian transition \
squares, every Y n -> X n finite (source hypothesis 1) and Y 0 -> S 0 proper (source hypothesis \
2), concluding the finite algebraization a : Z -> X proper over Spec A with every Y n the fibre \
product Z x_S S n. The halg binder of \
AlgebraicGeometry.exists_finite_algebraization_of_adicFiniteSystem is discharged here, by \
AlgebraicGeometry.adicFiniteAlgebraAlgebraization_holds"]
public theorem exists_finite_algebraization_of_adicFiniteSystem_holds
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (Y : ℕ → Scheme.{u}) (y : ∀ n, Y n ⟶ adicBaseChange A I f n)
    (t : ∀ n, Y n ⟶ Y (n + 1))
    (hcart : ∀ n, IsPullback (t n) (y n) (y (n + 1)) (adicBaseChangeSucc A I f n))
    (hfin : ∀ n, IsFinite (y n))
    (hproper : IsProper (y 0 ≫ pullback.snd f (adicThickeningι A I 0))) :
    ∃ (Z : Scheme.{u}) (a : Z ⟶ X), IsFinite a ∧ IsProper (a ≫ f) ∧
      ∃ k : ∀ n, Y n ⟶ Z,
        (∀ n, IsPullback (k n) (y n ≫ pullback.snd f (adicThickeningι A I n)) (a ≫ f)
          (adicThickeningι A I n)) ∧
        ∀ n, k n ≫ a = y n ≫ pullback.fst f (adicThickeningι A I n) :=
  exists_finite_algebraization_of_adicFiniteSystem A I f
    (adicFiniteAlgebraAlgebraization_holds A I f) Y y t hcart hfin hproper

/-! ### Stacks 0A42 -/

/-- **Algebraization of a compatible system of morphisms over the adic thickenings.** Let `A` be a
Noetherian ring complete with respect to an ideal `I`, write `S = Spec A` and `Sₙ = Spec (A / Iⁿ)`,
and let `fX : X ⟶ S` be proper and `fY : Y ⟶ S` separated of finite type. A compatible system of
morphisms `gₙ : Xₙ ⟶ Yₙ` over `Sₙ` comes from a unique morphism `g : X ⟶ Y` over `S` whose base
change to each `Sₙ` is `gₙ`. -/
@[stacks 0A42 "at the source's hypotheses and with no further input: A Noetherian and I-adically \
complete, fX : X -> Spec A proper (source hypothesis 1), fY : Y -> Spec A separated of finite \
type (source hypothesis 2), and a compatible system of morphisms over the adic thickenings, \
concluding that it comes from a unique morphism X -> Y over Spec A. The halg and hrig binders \
of AlgebraicGeometry.existsUnique_algebraization_adicBaseChangeMap are discharged here, by \
AlgebraicGeometry.adicFiniteAlgebraization_holds and \
Stacks.AdicClosedSubschemeRigidity.adicRigidity"]
public theorem existsUnique_algebraization_adicBaseChangeMap_holds
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (hcomplete : IsAdicComplete I A) {X Y : Scheme.{u}}
    (fX : X ⟶ Spec (.of A)) (fY : Y ⟶ Spec (.of A))
    [IsProper fX] [IsSeparated fY] [LocallyOfFiniteType fY] [QuasiCompact fY]
    (g : ∀ n, adicBaseChange A I fX n ⟶ adicBaseChange A I fY n)
    (g_over : ∀ n, g n ≫ pullback.snd fY (adicThickeningι A I n) =
      pullback.snd fX (adicThickeningι A I n))
    (g_compatible : ∀ n, adicBaseChangeSucc A I fX n ≫ g (n + 1) =
      g n ≫ adicBaseChangeSucc A I fY n) :
    ∃! algebraization : {h : X ⟶ Y // h ≫ fY = fX},
      ∀ n, adicBaseChangeMap A I algebraization.1 algebraization.2 n = g n :=
  have := hcomplete
  existsUnique_algebraization_adicBaseChangeMap A I hcomplete
    (adicFiniteAlgebraization_holds A I) (Stacks.AdicClosedSubschemeRigidity.adicRigidity A I)
    fX fY g g_over g_compatible

/-! ### Stacks 0899 -/

/-- **Algebraization of a cartesian system of closed immersions over the adic thickenings.** Let
`A` be a Noetherian ring complete with respect to an ideal `I`, write `S = Spec A` and
`Sₙ = Spec (A / Iⁿ)`, and let `f : X ⟶ S` be separated of finite type; put `Xₙ = X ×_S Sₙ`. Given a
system of morphisms `jₙ : Zₙ ⟶ Xₙ` with transition maps making every square over `Xₙ ⟶ Xₙ₊₁`
cartesian, with `j 0 : Z₀ ⟶ X₀` a closed immersion and `Z₀ ⟶ S₀` proper, there is a closed
immersion `g : W ⟶ X` with `W` proper over `S` recovering the system by base change. -/
@[stacks 0899 "at the source's hypotheses and with no further input: A Noetherian and I-adically \
complete, f : X -> Spec A separated of finite type (IsSeparated, LocallyOfFiniteType and \
QuasiCompact), a system j n : Z n -> X n with cartesian transition squares whose j 0 is a closed \
immersion (source hypothesis 1) and whose Z 0 -> S 0 is proper (source hypothesis 2), concluding \
a closed immersion g : W -> X with W proper over Spec A recovering the system by base change. The \
halg binder of AlgebraicGeometry.exists_closedImmersion_algebraization_of_isPullback is \
discharged here, by \
AlgebraicGeometry.adicFiniteSystemAlgebraization_of_adicFiniteAlgebraAlgebraization at \
AlgebraicGeometry.adicFiniteAlgebraAlgebraization_holds, and its hrig binder by \
AlgebraicGeometry.adicMorphismRigidity"]
public theorem exists_closedImmersion_algebraization_of_isPullback_holds
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (hcomplete : IsAdicComplete I A) {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (Z : ℕ → Scheme.{u}) (j : ∀ n, Z n ⟶ adicBaseChange A I f n) (t : ∀ n, Z n ⟶ Z (n + 1))
    (hcart : ∀ n, IsPullback (t n) (j n) (j (n + 1)) (adicBaseChangeSucc A I f n))
    (hclosed : IsClosedImmersion (j 0))
    (hproper : IsProper (j 0 ≫ pullback.snd f (adicThickeningι A I 0))) :
    ∃ (W : Scheme.{u}) (g : W ⟶ X) (k : ∀ n, Z n ⟶ W),
      IsClosedImmersion g ∧ IsProper (g ≫ f) ∧
      (∀ n, IsPullback (k n) (j n ≫ pullback.snd f (adicThickeningι A I n)) (g ≫ f)
        (adicThickeningι A I n)) ∧
      (∀ n, k n ≫ g = j n ≫ pullback.fst f (adicThickeningι A I n)) ∧
      ∀ n, t n ≫ k (n + 1) = k n :=
  have := hcomplete
  exists_closedImmersion_algebraization_of_isPullback A I f hcomplete
    (adicFiniteSystemAlgebraization_of_adicFiniteAlgebraAlgebraization A I f
      (adicFiniteAlgebraAlgebraization_holds A I f))
    (adicMorphismRigidity A I) Z j t hcart hclosed hproper

end AlgebraicGeometry

end
