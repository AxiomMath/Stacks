module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedModuleRestrictScalars
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesGradedPullback
public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.GradedPullbackModule
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.Quasicoherent.ReesGradedModule
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.Quasicoherent.ReesGradedModulePieces
public import StacksFrontier.AlgebraicGeometry.SymmetricPullback.Transpose
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorAlgebraPullbackIso
public import StacksFrontier.AlgebraicGeometry.GradedProperCohomology.RelativeSpecProper
public import StacksFrontier.AlgebraicGeometry.GradedProperCohomology.TwistVanishingInt

/-!
# The associated graded module of an ideal-power filtration on a fibre

Let
```
Z --i--> X
|g       |f
v        v
Y --j--> S
```
be a commutative square of schemes, let `ℐ` be a quasi-coherent sheaf of ideals on `S` and let
`ℱ` be a sheaf of `𝒪_X`-modules. Write `ℐ𝒪_X` for the inverse image ideal `ℐ.comap f`. This
file builds

`⨁ₙ i^*((ℐ𝒪_X)ⁿ ℱ)` as a graded module over `g^*(⨁ₙ ℐⁿ/ℐⁿ⁺¹)`.

For the square of [Stacks, Tag 0D2N] — `S = Spec A` for a local ring `A` with maximal ideal
`𝔪 = ℐ`, `j : Spec κ(y) ⟶ Spec A` the closed point, `f : X ⟶ Spec A` the proper morphism and
`Z = X_y` its fibre — the algebra is the **associated graded** `R̃ = ⨁ₙ 𝔪ⁿ/𝔪ⁿ⁺¹` of `𝔪` read as
a graded algebra sheaf on `Spec κ(y)`, and the module is

`⨁ₙ 𝔪ⁿℱ/𝔪ⁿ⁺¹ℱ`,

because the pullback of a quasi-coherent module along a closed immersion is its quotient by the
ideal (`Stacks.Conormal.pullbackSection_surjective` and
`Stacks.Conormal.pullbackSection_eq_zero_iff`) and `𝔪 · 𝔪ⁿℱ = 𝔪ⁿ⁺¹ℱ`. This is the graded-module
argument of
`Stacks.GradedProperCohomology.exists_isZero_Hgroup_tensorPowTwist_of_gradedAlgebraSections`,
part (2) of [Stacks, Tag 0897] with the base change and the properness of `f'` discharged.

## The three steps

Nothing here is new mathematics; the point is that the three steps compose.

1. **Upstairs on `X`** the ideal-power multiples `⨁ₙ (ℐ𝒪_X)ⁿℱ` are a graded module over the Rees
   algebra `⨁ₙ (ℐ𝒪_X)ⁿ` — `Stacks.Blowup.reesGradedModule`, which is [Stacks, Tag 02O7].
2. **Pulling back along `i`** turns that into a graded module over `i^*(⨁ₙ (ℐ𝒪_X)ⁿ)`, the
   conormal algebra of `i` for the inverse image ideal — `Stacks.Conormal.gradedPullbackModule`.
   The pieces become `i^*((ℐ𝒪_X)ⁿℱ)`, which is where the quotient happens.
3. **Restricting scalars** along a unital homomorphism
   `Θ : g^*(⨁ₙ ℐⁿ/ℐⁿ⁺¹) ⟶ i^*(⨁ₙ (ℐ𝒪_X)ⁿ)` makes it a graded module over the algebra the
   capstone wants — `SheafOfModules.GradedModule.restrictScalars`.

`Θ` costs nothing but the square. A unital homomorphism out of a pulled-back graded algebra is
the adjoint transpose of one into a pushforward (`Stacks.RingedSpace.transposeUnitalHom`), and
the pushforward of a graded algebra along a composite of morphisms of ringed spaces **is** the
composite of the pushforwards, by `rfl`. So transposing twice, along `g` and then along `j`,
reduces `Θ` to a homomorphism

`⨁ₙ ℐⁿ ⟶ (g ≫ j)_*(i^*(⨁ₙ (ℐ𝒪_X)ⁿ))`,

and `g ≫ j = i ≫ f` carries that to `(i ≫ f)_*`, where it is the inverse-image comparison of
Rees algebras of [Stacks, Tag 01OG] (`Stacks.Blowup.reesComapUnitalHom`) followed by the unit of
`i^* ⊣ i_*` (`Stacks.RingedSpace.unitUnitalHom`).

## Main definitions

* `Stacks.AssociatedGradedFibre.totalComparison`: the homomorphism
  `⨁ₙ ℐⁿ ⟶ (i ≫ f)_*(i^*(⨁ₙ (ℐ𝒪_X)ⁿ))`.
* `Stacks.AssociatedGradedFibre.fibreAlgebraHom`: **`Θ`**.
* `Stacks.AssociatedGradedFibre.fibreAssociatedGradedModule`: **`⨁ₙ i^*((ℐ𝒪_X)ⁿℱ)` as a graded
  `g^*(⨁ₙ ℐⁿ/ℐⁿ⁺¹)`-module.**

## Main results

* `Stacks.AssociatedGradedFibre.totalComparison_app`: the comparison on a homogeneous section of
  `ℐⁿ` is the pullback along `i` of its inverse image under `f`. This is the only description of
  it there is, and with `Stacks.RingedSpace.transposeApp_pullbackUnit` it determines `Θ`.
* `Stacks.AssociatedGradedFibre.fibreAssociatedGradedModule_piece`: the degree-`n` piece is
  `i^*((ℐ𝒪_X)ⁿℱ)`.
* `Stacks.AssociatedGradedFibre.fibreAssociatedGradedModule_smul`: the action is the action of
  the Rees module, pulled back and restricted along `Θ`.
* `Stacks.AssociatedGradedFibre.isQuasicoherent_piece_fibreAssociatedGradedModule` and
  `isZero_piece_fibreAssociatedGradedModule_of_neg`: the pieces are quasi-coherent when `ℱ` is,
  and vanish in negative degrees — two of the four hypotheses the capstone makes on its graded
  module.

## Implementation notes

The square is used through an auxiliary `Stacks.AssociatedGradedFibre.comparisonAlong`, which
takes the morphism `Z ⟶ S` as a *variable* together with an equation identifying it with
`i ≫ f`. That is what makes the transport along the square a `subst` rather than a cast: a
`▸` on `i ≫ f = g ≫ j` cannot be eliminated, because neither side is a variable, and every
statement about the transported homomorphism would then carry an irreducible `Eq.ndrec`.

The two further hypotheses the capstone makes on its graded module — finite type, and
quasi-coherence of the coproduct of the nonnegative pieces — are not proved here. They are
properties of `ℱ` and of the base, not of this construction: finite type needs `ℱ` coherent and
`ℐ` finitely generated, and the coproduct needs the pieces to be quasi-coherent together with
quasi-coherence of coproducts.

## Why [Stacks, Tag 0D2N] does not go through this module, and what not to revive

**This construction is correct and gated, and it is deliberately not on the route to
[Stacks, Tag 0D2N].** Do not "simplify" that route by reviving it; the reason is recorded here
because an architectural fork was spent finding it.

The pieces here are `𝒪_Z`-modules on the fibre, so the vanishing this feeds into part (2) of
[Stacks, Tag 0897] is a vanishing on `X_y`, while the consumer in [Stacks, Tag 0D2M] asks for one
on `X`. Carrying it across costs four further statements: the commutation of the ideal-power
multiple with the twist, `i_* i^* M ≅ M/𝓘M` for the fibre's closed immersion, finite type of this
module, and the identification of the ideal-power layer with the kernel of the adic tower's
transition map. The route taken instead keeps the graded pieces as `𝒪_X`-modules killed by `𝓘` —
where they are the transition kernels of the adic system, already a quasi-coherent graded module
of finite type by [Stacks, Tag 087Z] (`Stacks.Coherent.finiteTypeAssociatedGradedData`) — and
needs none of that transport, because the engine's ampleness hypothesis is about the **relative
spectrum** and not about `Z`, and `Spec_X(⨁ₙ 𝓘ⁿ/𝓘ⁿ⁺¹) ⟶ X` factors through the closed subscheme
cut out by `𝓘`, its structure map killing `𝓘`; so ampleness upstairs follows from ampleness on
the fibre alone, by [Stacks, Tag 0892] part (2).

**The fact that decided it, and the one a later reader will trip over:** the `𝒪_X`-side objects
are `private`. `Stacks.Coherent.AssociatedGradedData` carries no uniqueness or comparison clause,
so nothing identifies its `module` with any other graded module over the same algebra, and the
gap that leaves is avoided only by naming the concrete construction — but in
`StacksFrontier/AlgebraicGeometry/FormalGeometry/CoherentAdicSystem/AssociatedGraded.lean` both the
algebra (`conormalPushforward`) and the module (`transitionGradedModule`) of that construction are
private, the only public handle being the existence statement above. So the comparison of the two
routes turns on a visibility decision in that file rather than on mathematics, which is why
neither route is obviously cheaper from the outside.

Two points are worth keeping in view. Part (2) of
[Stacks, Tag 0897] quantifies its exponent `d₀` **after** the whole graded module, so no route may
instantiate the module at a twist `ℱ(d)` — the choice of `d` would precede itself. And
[Stacks, Tag 0D2N] grants ampleness **only on the fibre**, so any statement whose hypothesis is
ampleness on all of `X` is vacuous here however convenient its conclusion looks: that disqualifies
[Stacks, Tag 0B5T] clause (4), and also `Stacks.Coherent.HasAssociatedGradedTwistVanishing` and
hence [Stacks, Tag 0884] as it is formalized.

## References

* [Stacks Project, Tag 0D2N](https://stacks.math.columbia.edu/tag/0D2N)
* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
* [Stacks Project, Tag 02O7](https://stacks.math.columbia.edu/tag/02O7)
* [Stacks Project, Tag 01OG](https://stacks.math.columbia.edu/tag/01OG)
* [Stacks Project, Tag 0630](https://stacks.math.columbia.edu/tag/0630)
* [Stacks Project, Tag 0FQZ](https://stacks.math.columbia.edu/tag/0FQZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Blowup RingedSpaceModuleAdjunction
open SheafOfModules.GradedAlgebra (UnitalHom)

universe u

namespace Stacks.RingedSpace

open Stacks.SheafOfModules.TensorStalkRingedSpace

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- **The unit `A ⟶ f_*(f^*A)` of the adjunction, as a unital homomorphism of sheaves of graded
algebras**: the formal transpose of the identity of `f^*A`. Degreewise it is the unit of
`f^* ⊣ f_*` on sheaves of modules, by `Stacks.RingedSpace.untransposeUnitalHom_app`, which is
the degreewise comparison `Stacks.GradedComap.unitPieceComparison` read as a homomorphism of
sheaves of graded algebras rather than as a `PieceComparison`. -/
noncomputable def unitUnitalHom
    (A' : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf Y)) :
    _root_.SheafOfModules.GradedAlgebra.UnitalHom A'
      (pushforwardAlgebra f (pullbackGradedAlgebra f A')) :=
  untransposeUnitalHom f
    (_root_.SheafOfModules.GradedAlgebra.UnitalHom.id (pullbackGradedAlgebra f A'))

/-- The unit is the pullback-unit image on every local section. -/
lemma unitUnitalHom_app
    (A' : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf Y)) (n : ℤ)
    (V : (Opens Y.carrier)ᵒᵖ) (a : (A'.piece n).val.obj V) :
    ((unitUnitalHom f A').app n).val.app V a = pullbackUnit f (A'.piece n) V a :=
  _root_.Stacks.RingedSpace.homEquiv_val_app f (A'.piece n)
    ((pullbackGradedAlgebra f A').piece n) (𝟙 _) V a

end Stacks.RingedSpace

namespace Stacks.AssociatedGradedFibre

variable {Z X Y S : Scheme.{u}} (i : Z ⟶ X) (f : X ⟶ S) (g : Z ⟶ Y) (j : Y ⟶ S)
  (I : S.IdealSheafData)

/-- **The comparison `⨁ₙ ℐⁿ ⟶ (i ≫ f)_*(i^*(⨁ₙ (ℐ𝒪_X)ⁿ))`**: the inverse-image comparison of
Rees algebras of [Stacks, Tag 01OG] followed by the unit of `i^* ⊣ i_*`, pushed forward along
`f`.

Its target is stated along the composite `i ≫ f`, which is the pushforward along `f` of the
pushforward along `i` on the nose: the pushforward of a sheaf of graded algebras along a
morphism of ringed spaces takes multiplication and unit over the image opens, so composing two
of them is composing the preimage maps. -/
def totalComparison :
    UnitalHom (reesGradedAlgebra I)
      (Stacks.RingedSpace.pushforwardAlgebra (i ≫ f).toLRSHom.toShHom
        (Stacks.Conormal.gradedPullback i (reesGradedAlgebra (I.comap f)))) :=
  (reesComapUnitalHom f I).comp
    (Stacks.PullbackExteriorAlgebra.pushforwardUnitalHom f.toLRSHom.toShHom
      (Stacks.RingedSpace.unitUnitalHom i.toLRSHom.toShHom (reesGradedAlgebra (I.comap f))))

/-- **The only description of the comparison**: on a homogeneous section `a` of `ℐⁿ` over an open
`V` of `S` it is the pullback-unit image, along `i`, of the inverse image of `a` under `f`
(`Stacks.Blowup.reesPieceComap`). -/
theorem totalComparison_app (n : ℤ) (V : S.Opens) (a : (reesPiece I n).val.obj (op V)) :
    ((totalComparison i f I).app n).val.app (op V) a =
      Stacks.RingedSpace.pullbackUnit i.toLRSHom.toShHom (reesPiece (I.comap f) n)
        (op (f ⁻¹ᵁ V)) ((reesPieceComap f I n).val.app (op V) a) :=
  Stacks.RingedSpace.unitUnitalHom_app i.toLRSHom.toShHom (reesGradedAlgebra (I.comap f)) n
    (op (f ⁻¹ᵁ V)) ((reesPieceComap f I n).val.app (op V) a)

/-- The comparison of `Stacks.AssociatedGradedFibre.totalComparison`, read along a morphism
`m : Z ⟶ S` presented as the composite `i ≫ f`. Taking the morphism as a variable rather than
rewriting `i ≫ f` is what lets every statement about the result be proved by `subst`. -/
def comparisonAlong (m : Z ⟶ S) (hm : m = i ≫ f) :
    UnitalHom (reesGradedAlgebra I)
      (Stacks.RingedSpace.pushforwardAlgebra m.toLRSHom.toShHom
        (Stacks.Conormal.gradedPullback i (reesGradedAlgebra (I.comap f)))) := by
  subst hm
  exact totalComparison i f I

/-- Along the composite `i ≫ f` itself, `Stacks.AssociatedGradedFibre.comparisonAlong` is
`Stacks.AssociatedGradedFibre.totalComparison`. -/
@[simp] theorem comparisonAlong_self :
    comparisonAlong i f I (i ≫ f) rfl = totalComparison i f I := rfl

/-- **`Θ : g^*(⨁ₙ ℐⁿ/ℐⁿ⁺¹) ⟶ i^*(⨁ₙ (ℐ𝒪_X)ⁿ)`.** Two adjoint transposes of the comparison
`Stacks.AssociatedGradedFibre.totalComparison`, read along the other side `g ≫ j` of the
square. -/
def fibreAlgebraHom (hsq : i ≫ f = g ≫ j) :
    UnitalHom
      (Stacks.Conormal.gradedPullback g (Stacks.Conormal.gradedPullback j (reesGradedAlgebra I)))
      (Stacks.Conormal.gradedPullback i (reesGradedAlgebra (I.comap f))) :=
  Stacks.RingedSpace.transposeUnitalHom g.toLRSHom.toShHom
    (Stacks.RingedSpace.transposeUnitalHom
      (C := Stacks.RingedSpace.pushforwardAlgebra g.toLRSHom.toShHom
        (Stacks.Conormal.gradedPullback i (reesGradedAlgebra (I.comap f))))
      j.toLRSHom.toShHom (comparisonAlong i f I (g ≫ j) hsq.symm))

/-- **`⨁ₙ (ℐ𝒪_X)ⁿℱ / (ℐ𝒪_X)ⁿ⁺¹ℱ` on `Z`, as a graded module over `g^*(⨁ₙ ℐⁿ/ℐⁿ⁺¹)`.**

The pieces are the pullbacks along `i` of the ideal-power multiples `(ℐ𝒪_X)ⁿℱ`, and the action
is the action of [Stacks, Tag 02O7] pulled back along `i` and restricted along
`Stacks.AssociatedGradedFibre.fibreAlgebraHom`. At the fibre of [Stacks, Tag 0D2N] this is
`⨁ₙ 𝔪ⁿℱ/𝔪ⁿ⁺¹ℱ` over the associated graded `R̃ = ⨁ₙ 𝔪ⁿ/𝔪ⁿ⁺¹` pulled back to `X_y`. -/
def fibreAssociatedGradedModule (ℱ : X.Modules) (hsq : i ≫ f = g ≫ j) :
    SheafOfModules.GradedModule.{u, u, u}
      (Stacks.Conormal.gradedPullback g
        (Stacks.Conormal.gradedPullback j (reesGradedAlgebra I))) :=
  SheafOfModules.GradedModule.restrictScalars (fibreAlgebraHom i f g j I hsq)
    (Stacks.Conormal.gradedPullbackModule i (reesGradedModule (I.comap f) ℱ))

/-- **The degree-`n` piece is `i^*((ℐ𝒪_X)ⁿℱ)`.** -/
@[simp] theorem fibreAssociatedGradedModule_piece (ℱ : X.Modules) (hsq : i ≫ f = g ≫ j)
    (n : ℤ) :
    (fibreAssociatedGradedModule i f g j I ℱ hsq).piece n =
      (Scheme.Modules.pullback i).obj ((reesMultiple (I.comap f) n ℱ).toSheafOfModules) :=
  rfl

/-- **The action is the action of the Rees module, pulled back along `i` and restricted along
`Θ`.** -/
theorem fibreAssociatedGradedModule_smul (ℱ : X.Modules) (hsq : i ≫ f = g ≫ j) (n k : ℤ)
    (U : (Opens ↥Z)ᵒᵖ)
    (x : ((Scheme.Modules.pullback i).obj
      ((reesMultiple (I.comap f) n ℱ).toSheafOfModules)).val.obj U)
    (y : ((Stacks.Conormal.gradedPullback g
      (Stacks.Conormal.gradedPullback j (reesGradedAlgebra I))).piece k).val.obj U) :
    (fibreAssociatedGradedModule i f g j I ℱ hsq).smul n k U x y =
      (Stacks.Conormal.gradedPullbackModule i (reesGradedModule (I.comap f) ℱ)).smul n k U x
        (((fibreAlgebraHom i f g j I hsq).app k).val.app U y) :=
  rfl

/-- **The pieces are quasi-coherent when `ℱ` is**: the ideal-power multiples of a quasi-coherent
module are quasi-coherent (`Stacks.Blowup.isQuasicoherent_piece_reesGradedModule`) and the
pullback of a quasi-coherent module is quasi-coherent ([Stacks, Tag 01BG]). -/
theorem isQuasicoherent_piece_fibreAssociatedGradedModule (ℱ : X.Modules)
    [ℱ.IsQuasicoherent] (hsq : i ≫ f = g ≫ j) (n : ℤ) :
    ((fibreAssociatedGradedModule i f g j I ℱ hsq).piece n).IsQuasicoherent :=
  Stacks.Conormal.gradedPullbackModule_isQuasicoherent i (reesGradedModule (I.comap f) ℱ)
    (fun m => isQuasicoherent_piece_reesGradedModule (I.comap f) ℱ m) n

/-- **The pieces vanish in negative degrees**, because `(ℐ𝒪_X)ⁿℱ` is there the zero subsheaf of
`ℱ`. -/
theorem isZero_piece_fibreAssociatedGradedModule_of_neg (ℱ : X.Modules)
    (hsq : i ≫ f = g ≫ j) (n : ℤ) (hn : n < 0) :
    IsZero ((fibreAssociatedGradedModule i f g j I ℱ hsq).piece n) :=
  Stacks.Conormal.gradedPullbackModule_negative_isZero i (reesGradedModule (I.comap f) ℱ)
    (fun m hm => isZero_piece_reesGradedModule_of_neg (I.comap f) ℱ m hm) n hn

/-- **The coproduct of the nonnegative pieces is quasi-coherent when `ℱ` is.** Quasi-coherence of
modules on a scheme is closed under colimits of every shape
(`Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_colimit`), and a coproduct is a
colimit over a discrete category; no uniformity across the degrees has to be supplied. -/
theorem isQuasicoherent_coprod_fibreAssociatedGradedModule (ℱ : X.Modules)
    [ℱ.IsQuasicoherent] (hsq : i ≫ f = g ≫ j) :
    (∐ fun n : ℕ =>
      (fibreAssociatedGradedModule i f g j I ℱ hsq).piece (n : ℤ)).IsQuasicoherent :=
  Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_colimit
    (Discrete.functor fun n : ℕ =>
      (fibreAssociatedGradedModule i f g j I ℱ hsq).piece (n : ℤ))
    fun n => isQuasicoherent_piece_fibreAssociatedGradedModule i f g j I ℱ hsq (n.as : ℤ)

/-! ### The graded algebra the module lives over -/

/-- **The homogeneous multiplication of `g^*(⨁ₙ ℐⁿ/ℐⁿ⁺¹)`'s source algebra `⨁ₙ ℐⁿ/ℐⁿ⁺¹` is
commutative.** The Rees algebra's is (`Stacks.Blowup.reesMultiplication_comm`), and
commutativity passes to a degreewise pullback by `Stacks.Conormal.gradedPullback_mul_comm`. This
is the datum the relative spectrum of a graded algebra sheaf asks for before reading it as a
sheaf of commutative algebras, so it appears inside the hypotheses of the capstone of part (2)
of [Stacks, Tag 0897]. -/
theorem associatedGradedAlgebra_mul_comm (p q : ℤ) (W : (Opens ↥Y)ᵒᵖ)
    (a : ((Stacks.Conormal.gradedPullback j (reesGradedAlgebra I)).piece p).val.obj W)
    (b : ((Stacks.Conormal.gradedPullback j (reesGradedAlgebra I)).piece q).val.obj W) :
    HEq (((Stacks.Conormal.gradedPullback j (reesGradedAlgebra I)).mul p q).app W a b)
      (((Stacks.Conormal.gradedPullback j (reesGradedAlgebra I)).mul q p).app W b a) :=
  Stacks.Conormal.gradedPullback_mul_comm j (reesGradedAlgebra I) (reesMultiplication_comm I)
    p q W a b

/-- The pieces of `⨁ₙ ℐⁿ/ℐⁿ⁺¹` are quasi-coherent: those of the Rees algebra are
(`Stacks.Blowup.reesPiece_isQuasicoherent`) and the pullback of a quasi-coherent module is
quasi-coherent ([Stacks, Tag 01BG]). -/
theorem associatedGradedAlgebra_isQuasicoherent (n : ℤ) :
    ((Stacks.Conormal.gradedPullback j (reesGradedAlgebra I)).piece n).IsQuasicoherent :=
  Stacks.Conormal.gradedPullback_isQuasicoherent j (reesGradedAlgebra I)
    (reesPiece_isQuasicoherent I) n

/-- `⨁ₙ ℐⁿ/ℐⁿ⁺¹` is concentrated in nonnegative degrees. -/
theorem associatedGradedAlgebra_negative_isZero (n : ℤ) (hn : n < 0) :
    IsZero ((Stacks.Conormal.gradedPullback j (reesGradedAlgebra I)).piece n) :=
  Stacks.Conormal.gradedPullback_negative_isZero j (reesGradedAlgebra I)
    (reesPiece_negative_isZero I) n hn

end Stacks.AssociatedGradedFibre

namespace Stacks.GradedProperCohomology

open Stacks.Ample Stacks.RelativeVeryAmple Stacks.RelativeSpec Stacks.AffineAlgebraEquivalence
open Stacks.AlgebraicGeometry.FiniteTypeDominating
open Stacks.AmpleLocallyClosed (pullbackModule)
open Stacks.Conormal (gradedPullback)
open Stacks.AssociatedGradedFibre

variable {Z X S : Scheme.{u}} (i : Z ⟶ X) (f : X ⟶ S) {k : Type u} [CommRing k]
  (g : Z ⟶ Spec (CommRingCat.of k)) (j : Spec (CommRingCat.of k) ⟶ S) (I : S.IdealSheafData)

/-- **Part (2) of [Stacks, Tag 0897] at the fibre, for the associated graded module
`⨁ₙ ℐⁿℱ/ℐⁿ⁺¹ℱ`.**

`Stacks.GradedProperCohomology.exists_isZero_Hgroup_tensorPowTwist_of_gradedAlgebraSections`
applied with `𝓐' = ⨁ₙ ℐⁿ/ℐⁿ⁺¹` on `Spec k` and
`M = Stacks.AssociatedGradedFibre.fibreAssociatedGradedModule`: the commutativity and
quasi-coherence of the algebra are
`Stacks.AssociatedGradedFibre.associatedGradedAlgebra_mul_comm` and
`associatedGradedAlgebra_isQuasicoherent`, and two of the module's four hypotheses — vanishing
in negative degrees and quasi-coherence of the coproduct of the nonnegative pieces — are
`Stacks.AssociatedGradedFibre.isZero_piece_fibreAssociatedGradedModule_of_neg` and
`isQuasicoherent_coprod_fibreAssociatedGradedModule`.

What is left is what this construction cannot supply: the ring isomorphism `ρ` of a Noetherian
`k`-algebra `R` with the global sections of `⨁ₙ ℐⁿ/ℐⁿ⁺¹` and its compatibility `hρ` with the
structure maps, finite type `hft` of the module, quasi-coherence `hB` of the ungraded unit, local
Noetherianness of the relative spectrum, and ampleness `hL` upstairs. At the fibre of
[Stacks, Tag 0D2N] — `S = Spec A` for a Noetherian local `A` with maximal ideal `ℐ = 𝔪`,
`k = κ(y)`, `Z = X_y` and `R = Gr_𝔪(A)` — `ρ` is the identification of the associated graded ring
with those sections, `hL` is [Stacks, Tag 0892] part (2) from ampleness of `ℒ_y`, and `R` is
Noetherian by `AssociatedGraded.isNoetherianRing_gradedRing`. -/
theorem exists_isZero_Hgroup_tensorPowTwist_fibreAssociatedGraded
    [AlgebraSheaf.IsQuasicoherent (gradedAlgebraSheaf (Spec (CommRingCat.of k))
      (gradedPullback j (Stacks.Blowup.reesGradedAlgebra I))
      (associatedGradedAlgebra_mul_comm j I))]
    (hg : AlgebraicGeometry.IsProper g)
    {R : Type u} [CommRing R] [IsNoetherianRing R] [Algebra k R]
    (ρ : R ≃+* ↥((gradedAlgebraSheaf (Spec (CommRingCat.of k))
      (gradedPullback j (Stacks.Blowup.reesGradedAlgebra I))
      (associatedGradedAlgebra_mul_comm j I)).sections ⊤))
    (hρ : ∀ r : k, ρ (algebraMap k R r) =
      (gradedAlgebraSheaf (Spec (CommRingCat.of k))
        (gradedPullback j (Stacks.Blowup.reesGradedAlgebra I))
        (associatedGradedAlgebra_mul_comm j I)).unitTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv r))
    [(gradedPullback g (gradedPullback j (Stacks.Blowup.reesGradedAlgebra I))).IsCommutative]
    [AlgebraSheaf.IsQuasicoherent (pullbackGradedAlgebraSheaf g
      (gradedPullback j (Stacks.Blowup.reesGradedAlgebra I))
      (associatedGradedAlgebra_mul_comm j I))]
    [IsLocallyNoetherian (relativeSpecOver (pullbackGradedAlgebraSheaf g
      (gradedPullback j (Stacks.Blowup.reesGradedAlgebra I))
      (associatedGradedAlgebra_mul_comm j I))).left]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] (hsq : i ≫ f = g ≫ j)
    (hB : ((_root_.SheafOfModules.restrictScalars (gradedPullback g
          (gradedPullback j (Stacks.Blowup.reesGradedAlgebra I))).ungradedStructureMap).obj
        (_root_.SheafOfModules.unit
          (gradedPullback g
            (gradedPullback j (Stacks.Blowup.reesGradedAlgebra I))).ungradedSheaf)).IsQuasicoherent)
    (hft : (fibreAssociatedGradedModule i f g j I ℱ hsq).IsFiniteType)
    (L : Z.Modules) [IsInvertibleModule Z L]
    (hL : IsAmple (relativeSpecOver (pullbackGradedAlgebraSheaf g
        (gradedPullback j (Stacks.Blowup.reesGradedAlgebra I))
        (associatedGradedAlgebra_mul_comm j I))).left
      (pullbackModule (relativeSpecOver (pullbackGradedAlgebraSheaf g
        (gradedPullback j (Stacks.Blowup.reesGradedAlgebra I))
        (associatedGradedAlgebra_mul_comm j I))).hom L)) :
    ∃ d₀ : ℕ, ∀ d p : ℕ, d₀ ≤ d → 0 < p → ∀ n : ℕ,
      IsZero (Hgroup Z.ringCatSheaf ⊤ p
        (tensorModules Z ((fibreAssociatedGradedModule i f g j I ℱ hsq).piece (n : ℤ))
          (tensorPowModule Z L (d : ℤ)))) :=
  exists_isZero_Hgroup_tensorPowTwist_of_gradedAlgebraSections g
    (gradedPullback j (Stacks.Blowup.reesGradedAlgebra I))
    (associatedGradedAlgebra_mul_comm j I) (associatedGradedAlgebra_isQuasicoherent j I) hg ρ hρ
    (fibreAssociatedGradedModule i f g j I ℱ hsq) hB
    (isQuasicoherent_coprod_fibreAssociatedGradedModule i f g j I ℱ hsq)
    (fun n hn => isZero_piece_fibreAssociatedGradedModule_of_neg i f g j I ℱ hsq n hn) hft L hL

/-- **The same vanishing with the twist an arbitrary integer**, which is the form the dévissage
of [Stacks, Tag 0D2M] consumes.

`Stacks.GradedProperCohomology.exists_isZero_Hgroup_tensorPowTwist_fibreAssociatedGraded` read
through `exists_isZero_Hgroup_tensorPowTwist_int_of_nat`. Nothing is added: the natural-number
statement already serves every integer `d` above `(dₑ : ℤ)`, since such a `d` is nonnegative.

The `L` here is any invertible module on the fibre; at [Stacks, Tag 0D2N] it is the pullback
`i^* ℒ` of an invertible module on `X`, invertible by [Stacks, Tag 0B8P]. Keeping it general
is what separates this statement from the transport to `X`, which is where `i` enters. -/
theorem exists_isZero_Hgroup_tensorPowTwist_int_fibreAssociatedGraded
    [AlgebraSheaf.IsQuasicoherent (gradedAlgebraSheaf (Spec (CommRingCat.of k))
      (gradedPullback j (Stacks.Blowup.reesGradedAlgebra I))
      (associatedGradedAlgebra_mul_comm j I))]
    (hg : AlgebraicGeometry.IsProper g)
    {R : Type u} [CommRing R] [IsNoetherianRing R] [Algebra k R]
    (ρ : R ≃+* ↥((gradedAlgebraSheaf (Spec (CommRingCat.of k))
      (gradedPullback j (Stacks.Blowup.reesGradedAlgebra I))
      (associatedGradedAlgebra_mul_comm j I)).sections ⊤))
    (hρ : ∀ r : k, ρ (algebraMap k R r) =
      (gradedAlgebraSheaf (Spec (CommRingCat.of k))
        (gradedPullback j (Stacks.Blowup.reesGradedAlgebra I))
        (associatedGradedAlgebra_mul_comm j I)).unitTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv r))
    [(gradedPullback g (gradedPullback j (Stacks.Blowup.reesGradedAlgebra I))).IsCommutative]
    [AlgebraSheaf.IsQuasicoherent (pullbackGradedAlgebraSheaf g
      (gradedPullback j (Stacks.Blowup.reesGradedAlgebra I))
      (associatedGradedAlgebra_mul_comm j I))]
    [IsLocallyNoetherian (relativeSpecOver (pullbackGradedAlgebraSheaf g
      (gradedPullback j (Stacks.Blowup.reesGradedAlgebra I))
      (associatedGradedAlgebra_mul_comm j I))).left]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] (hsq : i ≫ f = g ≫ j)
    (hB : ((_root_.SheafOfModules.restrictScalars (gradedPullback g
          (gradedPullback j (Stacks.Blowup.reesGradedAlgebra I))).ungradedStructureMap).obj
        (_root_.SheafOfModules.unit
          (gradedPullback g
            (gradedPullback j (Stacks.Blowup.reesGradedAlgebra I))).ungradedSheaf)).IsQuasicoherent)
    (hft : (fibreAssociatedGradedModule i f g j I ℱ hsq).IsFiniteType)
    (L : Z.Modules) [IsInvertibleModule Z L]
    (hL : IsAmple (relativeSpecOver (pullbackGradedAlgebraSheaf g
        (gradedPullback j (Stacks.Blowup.reesGradedAlgebra I))
        (associatedGradedAlgebra_mul_comm j I))).left
      (pullbackModule (relativeSpecOver (pullbackGradedAlgebraSheaf g
        (gradedPullback j (Stacks.Blowup.reesGradedAlgebra I))
        (associatedGradedAlgebra_mul_comm j I))).hom L)) :
    ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d → ∀ p : ℕ, 0 < p → ∀ n : ℕ,
      IsZero (Hgroup Z.ringCatSheaf ⊤ p
        (tensorModules Z ((fibreAssociatedGradedModule i f g j I ℱ hsq).piece (n : ℤ))
          (tensorPowModule Z L d))) :=
  exists_isZero_Hgroup_tensorPowTwist_int_of_nat L
    (fun n => (fibreAssociatedGradedModule i f g j I ℱ hsq).piece (n : ℤ))
    (exists_isZero_Hgroup_tensorPowTwist_fibreAssociatedGraded i f g j I hg ρ hρ ℱ hsq hB hft L
      hL)

end Stacks.GradedProperCohomology

end
