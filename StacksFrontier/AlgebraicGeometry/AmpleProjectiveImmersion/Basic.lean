module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerCoherence
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwist
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpace
public import StacksFrontier.AlgebraicGeometry.AmpleWire.Basic
public import StacksFrontier.AlgebraicGeometry.InvertiblePullback.Basic

/-!
# Stacks Tag 01VS: embedding by high powers of an ample invertible sheaf, and what it still owes

Stacks Tag 01VS says that an ample invertible sheaf `L` on a scheme `X` locally of finite type
over a base `S` has all sufficiently high powers induced from the hyperplane sheaf by an
immersion `X ⟶ ℙⁿ_S` over `S`. This file states the tag over the library's objects and
reduces it to a single named condition, by discharging everything in it that is formal.

## What is formal, and is discharged here

Projective space over `S` is a fibre product over the terminal scheme, so a morphism into it is
a *pair* consisting of a morphism to `S` and a morphism to the integral model, with **no
commuting square to check**: the compatibility `CategoryTheory.Limits.pullback.lift` asks for is
an equality of two morphisms into the terminal object. Hence

* the clause of Tag 01VS that the immersion lies over `S` costs nothing — it is
  `Stacks.AmpleProjectiveImmersion.liftOver_fst`;
* every morphism `X ⟶ ℙⁿ_S` over `S` *is* such a pair, by
  `Stacks.AmpleProjectiveImmersion.liftOver_eq`, so nothing is lost by phrasing the tag through
  pairs rather than through an arbitrary morphism into `ℙⁿ_S`.

Consequently the tag is **equivalent** to a statement about morphisms to the integral model of
projective space together with an immersion condition, and that equivalence is proved, not
assumed: `Stacks.AmpleProjectiveImmersion.hasImmersionTwist_iff`.

## What remains, named

`Stacks.AmpleProjectiveImmersion.ImmersionTwistGap` is the one condition left, and it is the
geometric content of the source: the construction of the morphism to projective space out of
finitely many global sections of `L ^⊗ d` generating it, and the verification that it is an
immersion.

**That condition is reduced further**, to two conditions
neither of which is Tag 01VS, in
`StacksFrontier/AlgebraicGeometry/AmpleImmersionReduction/Basic.lean`:
`Stacks.AmpleImmersionReduction.immersionTwistGap_of_chartImmersionTwist`. The morphism itself is
available as well — see "What is not done".

## Main definitions

* `Stacks.AmpleProjectiveImmersion.twistingSheafAtUniverse`: `𝒪(1)` on the integral model of
  projective space, in the universe of the base.
* `Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf`: `𝒪(1)` on `ℙⁿ_S`, pulled back
  from the integral model. This is Tag 01VS's hyperplane sheaf.
* `Stacks.AmpleProjectiveImmersion.liftOver`: the morphism `X ⟶ ℙⁿ_S` attached to a structure
  morphism `f : X ⟶ S` and a morphism `g : X ⟶ ℙⁿ_ℤ`.
* `Stacks.AmpleProjectiveImmersion.tensorPowerModule`: Tag 01CU's tensor power of an invertible
  `𝒪_X`-module, with the invertibility class the ampleness theory uses converted to the one Tag
  01CU's construction asks for.
* `Stacks.AmpleProjectiveImmersion.HasImmersionTwist`,
  `Stacks.AmpleProjectiveImmersion.HasImmersionTwistOver`: the conclusion of Tag 01VS at a single
  degree, in the pair form and verbatim.
* `Stacks.AmpleProjectiveImmersion.EventualImmersionTwist`,
  `Stacks.AmpleProjectiveImmersion.ImmersionTwistGap`: **what Tag 01VS still owes.**

## Main results

* `Stacks.AmpleProjectiveImmersion.hasImmersionTwist_iff`: the pair form and the verbatim form of
  Tag 01VS's per-degree conclusion are equivalent. Both halves are proved; neither is assumed.
* `Stacks.AmpleProjectiveImmersion.isImmersion_lift`: a morphism into a fibre product is an
  immersion as soon as one of its two components is. This is the step by which the source turns
  the pair `(j, j')` into an immersion into `ℙᵐ_S ×_S ℙᵗ_S`.
* `Stacks.AmpleProjectiveImmersion.isImmersion_liftOver_of_isImmersion` and
  `Stacks.AmpleProjectiveImmersion.hasImmersionTwist_pullback_of_isImmersion`: the case of an
  immersion structure morphism, which witnesses that the condition below is satisfiable.
* `Stacks.AmpleProjectiveImmersion.liftOverTwistIso`: the hyperplane sheaf of `ℙⁿ_S` pulled back
  along `liftOver f g` is the hyperplane sheaf of the integral model pulled back along `g`.
* `Stacks.AmpleProjectiveImmersion.exists_immersion_projectiveSpaceOver_of_isAmple` and
  `Stacks.AmpleProjectiveImmersion.exists_immersion_projectiveSpaceOver_of_isAmple'`: **the
  statement of Tag 01VS**, with the auxiliary definitions of the source statement replaced by their
  library names and nothing else changed, from `ImmersionTwistGap`.
  The primed form uses the ampleness theory's own
  family of tensor powers in place of Tag 01CU's; see the implementation notes.

## Implementation notes

**Two Tag 01CS classes and two families of tensor powers.** The repository has two classes
labelled Tag 01CS — `Stacks.SheafOfModules.IsInvertible` and
`AlgebraicGeometry.SheafOfModules.IsInvertible` — and two constructions of the integer tensor
powers: `Stacks.SheafOfModules.TensorPower.tensorPower`, which carries the Tag 01CU attribute and
whose instance argument is the first class, and `AlgebraicGeometry.SheafOfModules.tensorPow`,
which the ampleness theory uses through `Stacks.Ample.tensorPowModule` and whose instance
argument is the second. `Stacks.AmpleProjectiveImmersion.tensorPowerModule` is Tag 01CU's power
with the instance supplied by the bridge
`Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible`; since
invertibility is a `Prop`-valued class this is Tag 01CU's declaration applied to *the* instance
and not to a choice. Both families appear below, in the two forms of the final theorem, because
the isomorphism between them, `Stacks.PowerFamilyBridge.tensorPowerModuleIso`, valid in every
integer degree, is proved downstream of this file.

**The twist comparison is composed in `Iso`.** `AlgebraicGeometry.Scheme.Modules.pullbackCongr`
is `eqToIso`, and the hazard for it is that asking the kernel to *convert* against it
forces evaluation of a transport of the pullback functor. `liftOverTwistIso` therefore only
composes it; no equation between morphisms is ever requested.

## What is not done

**What the library already supplies.**

1. The construction of a morphism to projective space from a generating family of global
   sections of an invertible sheaf, Stacks Tag 01NE, is
   `Stacks.ProjGlobalSectionsAppTop.exists_hom_projectiveSpaceOver_of_generatesStalks`
   (`../ProjGlobalSectionsAppTop/Consumers.lean:354`), unconditional: a morphism `X ⟶ ℙⁿ_S` over
   `S`, pinned on every chart, from a family of global sections of an arbitrary invertible `L`
   generating its stalks. What it does *not* assert is the twist identification
   `L ≅ p ^* 𝒪(1)`, and that — not the morphism — is what Tag 01VS still owes. Mathlib's
   `AlgebraicGeometry.Proj.fromOfGlobalSections` takes a ring map
   `A → Γ(X, ⊤)` and lands in the absolute `Proj`, so it gives the morphism only where `L ^⊗ d`
   is trivial. Tag 01NE itself is unattached, being a representability statement.
2. The graded section ring `Γ_*(X, L)` of Tag 01CV is
   `Stacks.GradedSections.sectionRing` (`../GradedSections/Monoidal.lean:255`), with its grading
   `Stacks.AmpleFiniteAvoidance.grading` and the ideals that graded prime avoidance is run on in
   `../AmpleFiniteAvoidance/Basic.lean`. The *tag* 01CV is unattached, but the object is
   available.
3. The Segre embedding of Tag 01WD is
   `Stacks.AlgebraicGeometry.SegreProdIso.exists_segreEmbedding`
   (`../SegreProdIso/Main.lean:377`), which carries the Tag 01WD attribute and hypothesises nothing
   beyond the base scheme; the conditional form
   `Stacks.AlgebraicGeometry.SegreGlue.exists_segreEmbedding_of_isIso_segreProd` is
   superseded, its hypothesis discharged by `SegreProdIso.isIso_segreProd`. What the Tag 01WD
   statement does *not* give is the identification of `𝒪(1)` along the Segre embedding, which is
   what the source's step 7 needs of it.
4. `ImmersionTwistGap` is
   reduced, to two conditions neither of which is Tag 01VS, by
   `Stacks.AmpleImmersionReduction.immersionTwistGap_of_chartImmersionTwist`
   (`../AmpleImmersionReduction/Basic.lean`); and at a single degree the reduction is to one
   condition, `Stacks.AmpleImmersionReduction.hasImmersionTwistOver_of_isAmple`.

`ImmersionTwistGap` is therefore still stated rather than proved in *this* file, and it is a
hypothesis of the two theorems below; it is not, however, where the argument
stops.

No comparison between the two families of tensor powers named above is proved *in this file*; a
proof of `ImmersionTwistGap` for one family does not transfer to the other without one. The
comparison is proved in `StacksDraft/AlgebraicGeometry/F3/PowerFamilyBridge/`, which is
downstream of this file, and the transfer is
`Stacks.PowerFamilyBridge.immersionTwistGap_iff`.

## References

* [Stacks Project, Tag 01VS](https://stacks.math.columbia.edu/tag/01VS)
* [Stacks Project, Tag 01NF](https://stacks.math.columbia.edu/tag/01NF)
* [Stacks Project, Tag 01MN](https://stacks.math.columbia.edu/tag/01MN)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01PS](https://stacks.math.columbia.edu/tag/01PS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.AmpleProjectiveImmersion

/-! ### The hyperplane sheaf -/

/-- The hyperplane sheaf `𝒪(1)` on the integral model of projective `n`-space, in the universe
of the base scheme. -/
abbrev twistingSheafAtUniverse (n : ℕ) : (projectiveSpaceAtUniverse.{u} n).Modules := by
  letI : GradedAlgebra
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) :=
    MvPolynomial.gradedAlgebra
  exact ProjectiveSpectrum.Proj.twistingSheaf
    (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) 1

/-- The hyperplane sheaf `𝒪(1)` on projective `n`-space over a scheme `S`: the pullback of the
degree-one twisting sheaf on the integral model along the projection to it. -/
abbrev projectiveSpaceTwistingSheaf (n : ℕ) (S : Scheme.{u}) :
    (projectiveSpaceOver n S).Modules :=
  (Scheme.Modules.pullback (projectiveSpaceOver.toIntegralAtUniverse n S)).obj
    (twistingSheafAtUniverse n)

/-! ### Immersions into a fibre product -/

/-- **A morphism into a fibre product is an immersion as soon as one of its two components is.**
This is the step by which Tag 01VS's proof turns the pair of an immersion `j : X ⟶ ℙᵐ_S` and an
arbitrary `j' : X ⟶ ℙᵗ_S` into an immersion `X ⟶ ℙᵐ_S ×_S ℙᵗ_S`. -/
theorem isImmersion_lift {X Y Z T : Scheme.{u}} {a : Y ⟶ T} {b : Z ⟶ T} (p : X ⟶ Y) (q : X ⟶ Z)
    (h : p ≫ a = q ≫ b) [IsImmersion p] : IsImmersion (pullback.lift p q h) := by
  have : IsImmersion (pullback.lift p q h ≫ pullback.fst a b) := by rwa [pullback.lift_fst]
  exact IsImmersion.of_comp (pullback.lift p q h) (pullback.fst a b)

/-! ### Morphisms to projective space over a base -/

section Lift

variable {X S : Scheme.{u}} (f : X ⟶ S) {n : ℕ} (g : X ⟶ projectiveSpaceAtUniverse.{u} n)

/-- The morphism `X ⟶ ℙⁿ_S` attached to a morphism `f : X ⟶ S` and a morphism `g` to the
integral model of projective space. No compatibility has to be checked: `ℙⁿ_S` is a fibre product
over the terminal scheme, so the condition is an equality of morphisms into a terminal object. -/
def liftOver : X ⟶ projectiveSpaceOver n S :=
  pullback.lift f g (terminal.hom_ext _ _)

/-- `liftOver f g` lies over `S` by construction. This is the clause of Tag 01VS asserting that
the immersion is a morphism of `S`-schemes. -/
@[simp] theorem liftOver_fst :
    liftOver f g ≫ pullback.fst (terminal.from S)
      (terminal.from (projectiveSpaceAtUniverse.{u} n)) = f :=
  pullback.lift_fst _ _ _

/-- `liftOver f g` induces `g` on the integral model. -/
@[simp] theorem liftOver_snd :
    liftOver f g ≫ projectiveSpaceOver.toIntegralAtUniverse n S = g :=
  pullback.lift_snd _ _ _

/-- **Every morphism to `ℙⁿ_S` over `S` is a `liftOver`.** So phrasing Tag 01VS through pairs
loses nothing. -/
theorem liftOver_eq (i : X ⟶ projectiveSpaceOver n S)
    (h : i ≫ pullback.fst (terminal.from S)
      (terminal.from (projectiveSpaceAtUniverse.{u} n)) = f) :
    liftOver f (i ≫ projectiveSpaceOver.toIntegralAtUniverse n S) = i :=
  pullback.hom_ext (by rw [liftOver_fst, h]) (by rw [liftOver_snd])

/-- **If the structure morphism is an immersion then so is every `liftOver f g`.** The case
`p = f` of `Stacks.AmpleProjectiveImmersion.isImmersion_lift`. -/
theorem isImmersion_liftOver_of_isImmersion [IsImmersion f] : IsImmersion (liftOver f g) :=
  isImmersion_lift f g (terminal.hom_ext _ _)

/-- **If the morphism to the integral model is an immersion then so is `liftOver f g`.** This is
the handle an absolute construction of `g` would use, and it is *strictly stronger* than Tag 01VS
needs: `ℙⁿ_k ⟶ ℙⁿ_ℤ` is an immersion over `S = Spec k` and is not an immersion absolutely. So the
condition left open below is not this one. -/
theorem isImmersion_liftOver_of_isImmersion_integralModel [IsImmersion g] :
    IsImmersion (liftOver f g) := by
  have : IsImmersion (liftOver f g ≫ projectiveSpaceOver.toIntegralAtUniverse n S) := by
    rwa [liftOver_snd]
  exact IsImmersion.of_comp (liftOver f g) (projectiveSpaceOver.toIntegralAtUniverse n S)

/-- **The hyperplane sheaf of `ℙⁿ_S` pulled back along `liftOver f g` is the hyperplane sheaf of
the integral model pulled back along `g`**, by pseudofunctoriality of the module pullback and
`Stacks.AmpleProjectiveImmersion.liftOver_snd`. -/
def liftOverTwistIso :
    (Scheme.Modules.pullback (liftOver f g)).obj (projectiveSpaceTwistingSheaf n S) ≅
      (Scheme.Modules.pullback g).obj (twistingSheafAtUniverse n) :=
  (Scheme.Modules.pullbackComp (liftOver f g)
      (projectiveSpaceOver.toIntegralAtUniverse n S)).app (twistingSheafAtUniverse n) ≪≫
    (Scheme.Modules.pullbackCongr (liftOver_snd f g)).app (twistingSheafAtUniverse n)

end Lift

/-! ### Tag 01CU's tensor powers through the bridge of the two Tag 01CS classes -/

/-- **Tag 01CU's `d`-th tensor power of an invertible `𝒪_X`-module**, with the invertibility
class of the ampleness theory converted to the one Tag 01CU's construction takes, by
`Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible`. Invertibility is
a `Prop`-valued class, so this is Tag 01CU's declaration applied to *the* instance rather than to
a choice of one. -/
abbrev tensorPowerModule (X : Scheme.{u}) (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (d : ℤ) : X.Modules := by
  have hL : Stacks.SheafOfModules.IsInvertible X.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) L :=
    (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible
      X.presheaf (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) L).mpr inferInstance
  letI := Stacks.SheafOfModules.TensorPower.isEquivalence_tensorRightFunctor X.presheaf
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) L
  exact Stacks.SheafOfModules.TensorPower.tensorPower X.presheaf
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) L d

/-! ### Tag 01VS at a single degree -/

variable {X S : Scheme.{u}} (f : X ⟶ S) (M : X.Modules)

/-- **Tag 01VS's conclusion at a single degree, in pair form.** There is a morphism `g` to the
integral model of some projective space such that the induced morphism to projective space over
`S` is an immersion carrying the hyperplane sheaf to `M`. -/
def HasImmersionTwist : Prop :=
  ∃ (n : ℕ) (g : X ⟶ projectiveSpaceAtUniverse.{u} n), IsImmersion (liftOver f g) ∧
    Nonempty (M ≅
      (Scheme.Modules.pullback (liftOver f g)).obj (projectiveSpaceTwistingSheaf n S))

/-- **Tag 01VS's conclusion at a single degree, verbatim**: an immersion into projective space
over `S`, lying over `S`, pulling the hyperplane sheaf back to `M`. -/
def HasImmersionTwistOver : Prop :=
  ∃ (n : ℕ) (i : X ⟶ projectiveSpaceOver n S), IsImmersion i ∧
    i ≫ pullback.fst (terminal.from S)
      (terminal.from (projectiveSpaceAtUniverse.{u} n)) = f ∧
    Nonempty (M ≅ (Scheme.Modules.pullback i).obj (projectiveSpaceTwistingSheaf n S))

/-- **The pair form and the verbatim form of Tag 01VS's per-degree conclusion agree.** Forwards,
the clause over `S` is `Stacks.AmpleProjectiveImmersion.liftOver_fst`; backwards, the morphism is
recovered as a pair by `Stacks.AmpleProjectiveImmersion.liftOver_eq`. -/
theorem hasImmersionTwist_iff : HasImmersionTwist f M ↔ HasImmersionTwistOver f M := by
  constructor
  · rintro ⟨n, g, hi, e⟩
    exact ⟨n, liftOver f g, hi, liftOver_fst f g, e⟩
  · rintro ⟨n, i, hi, hf, e⟩
    rw [← liftOver_eq f i hf] at hi e
    exact ⟨n, _, hi, e⟩

/-- **`Stacks.AmpleProjectiveImmersion.HasImmersionTwist` is satisfiable.** When the structure
morphism is an immersion, every pullback of the hyperplane sheaf along a `liftOver` satisfies it.
Recorded because the reduction below would otherwise be a reduction to a condition not known to
hold of anything. -/
theorem hasImmersionTwist_pullback_of_isImmersion [IsImmersion f] {n : ℕ}
    (g : X ⟶ projectiveSpaceAtUniverse.{u} n) :
    HasImmersionTwist f
      ((Scheme.Modules.pullback (liftOver f g)).obj (projectiveSpaceTwistingSheaf n S)) :=
  ⟨n, g, isImmersion_liftOver_of_isImmersion f g, ⟨Iso.refl _⟩⟩

/-! ### What Tag 01VS still owes -/

/-- All sufficiently high members of a family of `𝒪_X`-modules satisfy
`Stacks.AmpleProjectiveImmersion.HasImmersionTwist`. -/
def EventualImmersionTwist (pow : ℤ → X.Modules) : Prop :=
  ∃ d₀ : ℕ, 1 ≤ d₀ ∧ ∀ d : ℕ, d₀ ≤ d → HasImmersionTwist f (pow (d : ℤ))

/-- **What Stacks Tag 01VS still owes.** For an ample invertible `𝒪_X`-module on a scheme locally
of finite type over `S`, all sufficiently high tensor powers are the hyperplane sheaf pulled back
along a morphism to projective space over `S` that is an immersion.

Everything formal has been removed: the clause that the immersion lies over `S`, and the passage
between an arbitrary morphism to `ℙⁿ_S` and a pair, are discharged by
`Stacks.AmpleProjectiveImmersion.hasImmersionTwist_iff`. What is left is the geometric content of
the source — the morphism to projective space built from finitely many generating global sections
of `L ^⊗ d`, and its being an immersion — which the repository cannot yet construct; see the
module docstring. -/
def ImmersionTwistGap (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
    (pow : ℤ → X.Modules) : Prop :=
  Stacks.Ample.IsAmple X L → LocallyOfFiniteType f → EventualImmersionTwist f pow

/-- An eventual `HasImmersionTwist` of a family of modules gives the verbatim Tag 01VS form. -/
private theorem exists_immersion_of_eventualImmersionTwist {pow : ℤ → X.Modules}
    (h : EventualImmersionTwist f pow) :
    ∃ d₀ : ℕ, 1 ≤ d₀ ∧ ∀ d : ℕ, d₀ ≤ d →
      ∃ (n : ℕ) (i : X ⟶ projectiveSpaceOver n S),
        IsImmersion i ∧
        i ≫ pullback.fst (terminal.from S)
          (terminal.from (projectiveSpaceAtUniverse.{u} n)) = f ∧
        Nonempty (pow (d : ℤ) ≅
          (Scheme.Modules.pullback i).obj (projectiveSpaceTwistingSheaf n S)) := by
  obtain ⟨d₀, hd₀, hd⟩ := h
  exact ⟨d₀, hd₀, fun d hdd => (hasImmersionTwist_iff f _).mp (hd d hdd)⟩

/-- **Stacks Tag 01VS**, from `Stacks.AmpleProjectiveImmersion.ImmersionTwistGap`. Every
sufficiently high tensor power of an ample invertible sheaf on a scheme locally of finite type
over `S` is the pullback of `𝒪(1)` along an immersion into projective space over `S`, lying over
`S`.

The conclusion is the tagged statement with its auxiliary definitions replaced by their library
names and nothing else changed. The tensor powers are Tag 01CU's, through
`Stacks.AmpleProjectiveImmersion.tensorPowerModule`. -/
theorem exists_immersion_projectiveSpaceOver_of_isAmple (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (hL : Stacks.Ample.IsAmple X L)
    [hf : LocallyOfFiniteType f] (h : ImmersionTwistGap f L (tensorPowerModule X L)) :
    ∃ d₀ : ℕ, 1 ≤ d₀ ∧ ∀ d : ℕ, d₀ ≤ d →
      ∃ (n : ℕ) (i : X ⟶ projectiveSpaceOver n S),
        IsImmersion i ∧
        i ≫ pullback.fst (terminal.from S)
          (terminal.from (projectiveSpaceAtUniverse.{u} n)) = f ∧
        Nonempty (tensorPowerModule X L (d : ℤ) ≅
          (Scheme.Modules.pullback i).obj (projectiveSpaceTwistingSheaf n S)) := by
  exact exists_immersion_of_eventualImmersionTwist f (h hL hf)

/-- **Stacks Tag 01VS** with the ampleness theory's own family of tensor powers,
`Stacks.Ample.tensorPowModule`, in place of Tag 01CU's. Stated separately because when this file
was written no isomorphism between the two families was available, so neither form implied the
other. One is available now, in every integer degree
(`Stacks.PowerFamilyBridge.tensorPowerModuleIso`), and the two forms are interderivable by
`Stacks.PowerFamilyBridge.exists_immersion_tensorPowModule_of_isAmple` and
`Stacks.PowerFamilyBridge.exists_immersion_tensorPowerModule_of_isAmple`. -/
theorem exists_immersion_projectiveSpaceOver_of_isAmple' (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (hL : Stacks.Ample.IsAmple X L)
    [hf : LocallyOfFiniteType f] (h : ImmersionTwistGap f L (Stacks.Ample.tensorPowModule X L)) :
    ∃ d₀ : ℕ, 1 ≤ d₀ ∧ ∀ d : ℕ, d₀ ≤ d →
      ∃ (n : ℕ) (i : X ⟶ projectiveSpaceOver n S),
        IsImmersion i ∧
        i ≫ pullback.fst (terminal.from S)
          (terminal.from (projectiveSpaceAtUniverse.{u} n)) = f ∧
        Nonempty (Stacks.Ample.tensorPowModule X L (d : ℤ) ≅
          (Scheme.Modules.pullback i).obj (projectiveSpaceTwistingSheaf n S)) := by
  exact exists_immersion_of_eventualImmersionTwist f (h hL hf)

end Stacks.AmpleProjectiveImmersion

end
