module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AmpleProjectiveImmersion.Basic
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FormalClosedSubschemeAlgebraization
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.Projective

/-!
# The ambient projective space of Grothendieck's algebraization theorem

We define the projective space `ℙᴺ_S` over `S = Spec A` and its structure morphism, and show that
it is H-projective and proper over `S`. Given a tower of schemes `Xₙ` over the thickenings `Sₙ` of
`S` with cartesian squares, and a compatible tower of morphisms `gₙ : Xₙ ⟶ ℙᴺ_ℤ` to the integral
model, we construct the induced morphisms `Xₙ ⟶ ℙᴺ_S ×_S Sₙ` into the adic base changes of `ℙᴺ_S`
and show that their squares over the transition maps are cartesian.

## Main definitions

* `Stacks.AmpleFormalSystemAmbient.ambient` and
  `Stacks.AmpleFormalSystemAmbient.ambientHom` — the scheme `ℙᴺ_{Spec A}` and its structure
  morphism to `Spec A`.
* `Stacks.AmpleFormalSystemAmbient.toAmbient` — the morphism `Y ⟶ ℙᴺ_{Spec A}` attached to a
  morphism `Y ⟶ Sₙ` and a morphism `Y ⟶ ℙᴺ_ℤ`.
* `Stacks.AmpleFormalSystemAmbient.adicLift` — the same datum read as a morphism into the `n`-th
  adic base change `ℙᴺ_S ×_S Sₙ` of the ambient scheme.

## Main results

* `Stacks.AmpleFormalSystemAmbient.isProjectiveMorphism_ambientHom` and
  `Stacks.AmpleFormalSystemAmbient.isProper_ambientHom` — the ambient scheme is H-projective, and
  hence proper, over `Spec A`.
* `Stacks.AmpleFormalSystemAmbient.isPullback_adicLift` — given a tower of schemes `Xₙ` over the
  thickenings with cartesian squares and a compatible tower of morphisms `gₙ : Xₙ ⟶ ℙᴺ_ℤ`, the
  induced morphisms `Xₙ ⟶ ℙᴺ_S ×_S Sₙ` have cartesian squares over the transition maps
  `AlgebraicGeometry.adicBaseChangeSucc`.

## References

* [Stacks Project, Tag 089A](https://stacks.math.columbia.edu/tag/089A)
* [Stacks Project, Tag 0899](https://stacks.math.columbia.edu/tag/0899)
* [Stacks Project, Tag 01NF](https://stacks.math.columbia.edu/tag/01NF)
* [Stacks Project, Tag 01W8](https://stacks.math.columbia.edu/tag/01W8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.AmpleFormalSystemAmbient

variable (A : Type u) [CommRing A] (I : Ideal A) (N : ℕ)

/-! ### The ambient scheme -/

/-- The projective space `ℙᴺ_{Spec A}` over `Spec A`. -/
public abbrev ambient : Scheme.{u} := projectiveSpaceOver N (Spec (.of A))

/-- The structure morphism `ℙᴺ_{Spec A} ⟶ Spec A`. -/
public abbrev ambientHom : ambient A N ⟶ Spec (.of A) := ambient A N ↘ Spec (.of A)

/-- **The ambient scheme is H-projective over `Spec A`.** -/
public theorem isProjectiveMorphism_ambientHom : IsProjectiveMorphism (ambientHom A N) :=
  ⟨N, 𝟙 _, inferInstance, Category.id_comp _⟩

/-- **The ambient scheme is proper over `Spec A`.** -/
public instance isProper_ambientHom : IsProper (ambientHom A N) :=
  isProper_projectiveSpaceOver N _

/-! ### Morphisms into the ambient scheme and into its adic base changes -/

variable {A I N}
variable {Y : Scheme.{u}} {n : ℕ}

/-- The morphism `Y ⟶ ℙᴺ_{Spec A}` attached to a morphism `q : Y ⟶ Sₙ` to a thickening and a
morphism `g : Y ⟶ ℙᴺ_ℤ` to the integral model. -/
public def toAmbient (q : Y ⟶ adicThickening A I n)
    (g : Y ⟶ projectiveSpaceAtUniverse.{u} N) : Y ⟶ ambient A N :=
  Stacks.AmpleProjectiveImmersion.liftOver (q ≫ adicThickeningι A I n) g

/-- `toAmbient q g` lies over `Spec A` through `q`. -/
@[simp] public lemma toAmbient_ambientHom (q : Y ⟶ adicThickening A I n)
    (g : Y ⟶ projectiveSpaceAtUniverse.{u} N) :
    toAmbient q g ≫ ambientHom A N = q ≫ adicThickeningι A I n :=
  Stacks.AmpleProjectiveImmersion.liftOver_fst _ _

/-- `toAmbient q g` induces `g` on the integral model. -/
@[simp] public lemma toAmbient_toIntegralAtUniverse (q : Y ⟶ adicThickening A I n)
    (g : Y ⟶ projectiveSpaceAtUniverse.{u} N) :
    toAmbient q g ≫ projectiveSpaceOver.toIntegralAtUniverse N (Spec (.of A)) = g :=
  Stacks.AmpleProjectiveImmersion.liftOver_snd _ _

/-- The morphism `Y ⟶ ℙᴺ_S ×_S Sₙ` attached to `q : Y ⟶ Sₙ` and `g : Y ⟶ ℙᴺ_ℤ`. -/
public def adicLift (q : Y ⟶ adicThickening A I n)
    (g : Y ⟶ projectiveSpaceAtUniverse.{u} N) :
    Y ⟶ adicBaseChange A I (ambientHom A N) n :=
  pullback.lift (toAmbient q g) q (toAmbient_ambientHom q g)

/-- The first projection of `adicLift q g` is `toAmbient q g`. -/
@[simp] public lemma adicLift_fst (q : Y ⟶ adicThickening A I n)
    (g : Y ⟶ projectiveSpaceAtUniverse.{u} N) :
    adicLift q g ≫ pullback.fst (ambientHom A N) (adicThickeningι A I n) = toAmbient q g :=
  pullback.lift_fst _ _ _

/-- The second projection of `adicLift q g` is `q`. -/
@[simp] public lemma adicLift_snd (q : Y ⟶ adicThickening A I n)
    (g : Y ⟶ projectiveSpaceAtUniverse.{u} N) :
    adicLift q g ≫ pullback.snd (ambientHom A N) (adicThickeningι A I n) = q :=
  pullback.lift_snd _ _ _

/-! ### The cartesian tower -/

variable (A I N)

/-- **A compatible tower of morphisms to the integral model induces a compatible tower of
morphisms into the ambient scheme.** -/
public lemma toAmbient_comp {Xn : ℕ → Scheme.{u}} (q : ∀ n, Xn n ⟶ adicThickening A I n)
    (i : ∀ n, Xn n ⟶ Xn (n + 1))
    (hq : ∀ n, i n ≫ q (n + 1) = q n ≫ adicThickeningSucc A I n)
    (g : ∀ n, Xn n ⟶ projectiveSpaceAtUniverse.{u} N)
    (hg : ∀ n, i n ≫ g (n + 1) = g n) (n : ℕ) :
    i n ≫ toAmbient (A := A) (I := I) (N := N) (q (n + 1)) (g (n + 1)) =
      toAmbient (q n) (g n) := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc]
    show i n ≫ toAmbient (q (n + 1)) (g (n + 1)) ≫ ambientHom A N = _
    rw [toAmbient_ambientHom, ← Category.assoc, hq n, Category.assoc, adicThickeningSucc_ι]
    exact (toAmbient_ambientHom (q n) (g n)).symm
  · rw [Category.assoc, toAmbient_toIntegralAtUniverse, hg n,
      toAmbient_toIntegralAtUniverse]

/-- The induced tower of morphisms into the adic base changes commutes with the transition
maps. -/
public lemma adicLift_comp {Xn : ℕ → Scheme.{u}} (q : ∀ n, Xn n ⟶ adicThickening A I n)
    (i : ∀ n, Xn n ⟶ Xn (n + 1))
    (hq : ∀ n, i n ≫ q (n + 1) = q n ≫ adicThickeningSucc A I n)
    (g : ∀ n, Xn n ⟶ projectiveSpaceAtUniverse.{u} N)
    (hg : ∀ n, i n ≫ g (n + 1) = g n) (n : ℕ) :
    i n ≫ adicLift (A := A) (I := I) (N := N) (q (n + 1)) (g (n + 1)) =
      adicLift (q n) (g n) ≫ adicBaseChangeSucc A I (ambientHom A N) n := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, adicLift_fst, Category.assoc, adicBaseChangeSucc_fst, adicLift_fst]
    exact toAmbient_comp A I N q i hq g hg n
  · rw [Category.assoc, adicLift_snd, Category.assoc, adicBaseChangeSucc,
      pullback.lift_snd, ← Category.assoc, adicLift_snd]
    exact hq n

/-- **The cartesian tower into the adic base changes of the ambient scheme.**

Let `Xₙ` be a tower of schemes over the thickenings `Sₙ` whose squares are cartesian, and let
`gₙ : Xₙ ⟶ ℙᴺ_ℤ` be a compatible tower of morphisms to the integral model. Then the induced
morphisms `Xₙ ⟶ ℙᴺ_S ×_S Sₙ` have cartesian squares over the transition maps
`AlgebraicGeometry.adicBaseChangeSucc`. -/
public lemma isPullback_adicLift {Xn : ℕ → Scheme.{u}} (q : ∀ n, Xn n ⟶ adicThickening A I n)
    (i : ∀ n, Xn n ⟶ Xn (n + 1))
    (hcart : ∀ n, IsPullback (i n) (q n) (q (n + 1)) (adicThickeningSucc A I n))
    (g : ∀ n, Xn n ⟶ projectiveSpaceAtUniverse.{u} N)
    (hg : ∀ n, i n ≫ g (n + 1) = g n) (n : ℕ) :
    IsPullback (i n) (adicLift (A := A) (I := I) (N := N) (q n) (g n))
      (adicLift (q (n + 1)) (g (n + 1))) (adicBaseChangeSucc A I (ambientHom A N) n) := by
  refine IsPullback.of_bot ?_
    (adicLift_comp A I N q i (fun m => (hcart m).w) g hg n)
    (isPullback_adicBaseChangeSucc A I (ambientHom A N) n)
  rw [adicLift_snd, adicLift_snd]
  exact hcart n

end Stacks.AmpleFormalSystemAmbient

end
