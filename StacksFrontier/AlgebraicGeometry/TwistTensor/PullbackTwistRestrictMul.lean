module

public import StacksFrontier.AlgebraicGeometry.TwistTensor.PullbackTwistPowerFactors
public import StacksFrontier.AlgebraicGeometry.TwistTensor.ThetaMultiplicativity
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorComparisonComp

/-!
# The contraction of the pullback along a composite is multiplicative

`Stacks.AlgebraicGeometry.PullbackTwistPower.pullbackTwistRestrictIso` is the first of the five
factors of `Stacks.AlgebraicGeometry.PullbackTwistPower.pullbackTwistPowIso`, the identification
`φ^*𝒪(dn) ≅ L^{⊗ n}` of [Stacks, Tag 01N8]: it contracts the pullback along
`Y ⟶ U_d ⟶ Proj 𝒮` into the pullback along `φ` of the restricted twist. What property (1) of
[Stacks, Tag 01O7] needs of the composite is its behaviour across degrees, and for this factor
that behaviour is multiplicativity: the contraction must carry the multiplication of the
pulled-back twists to the multiplication of the pullbacks of the restricted twists.

The implementation notes of
`StacksFrontier/AlgebraicGeometry/TwistTensor/PullbackTwistPowerFactors.lean` record that this
statement "is not formed anywhere" and name its ingredient,
`Stacks.PullbackTensorCoherence.pullbackCompIso`. It is formed here, for an arbitrary morphism
of modules in place of the twist multiplication, so that no invertibility of the multiplication
is needed.

## Main results

* `...PullbackTwistPower.pullbackComp_tensorator`: **the composition law for pullback of
  sheaves of modules on schemes is compatible with the comparison of [Stacks, Tag 01CD]**, in
  the scheme spelling. This is
  `Stacks.PullbackTensorCoherence.pullbackTensorComparison_comp` read at
  `AlgebraicGeometry.Scheme.Modules.pullbackComp`.
* `...PullbackTwistPower.pullbackComp_mul`: **the composition law is multiplicative for any
  multiplication induced by a morphism on the base.** Given `u : A ⊗ B ⟶ C` on `Z`, both
  `(p ≫ q)^*` and `p^* q^*` carry it to a multiplication of the pullbacks, by inverting the
  comparison of Tag 01CD and applying `u`; the composition law intertwines the two.
* `...PullbackTwistPower.pullbackTwistRestrictIso_mul`: **the contraction of the pullback along
  `Y ⟶ U_d ⟶ Proj 𝒮` is multiplicative**, which is the above at the factorisation
  `toProj 𝒮 φ = φ ≫ (Proj.degreeOpen 𝒮 d).ι`.
* `Stacks.Monoidal.contractionMul_free`: the square chase the three above run on, with every
  object and morphism a variable.

## Implementation notes

**The chase is done with free variables.** At the concrete objects the terms are large enough
that `rw [← Iso.eq_inv_comp]` on the goal exceeds the heartbeat allowance in `whnf` before it
fires. `Stacks.Monoidal.contractionMul_free` states the same rearrangement in an arbitrary
monoidal category, where every term is a variable, and the concrete statements are instances of
it; this is the discipline the free-object helpers of
`StacksFrontier/AlgebraicGeometry/TwistTensor/ThetaIntegerBidegree.lean` are written in.

**The two spellings of the pullback-composition isomorphism need no bridge.**
`AlgebraicGeometry.Scheme.Modules.pullbackComp p q` and
`Stacks.DerivedPullback.Composition.modulePullbackComp p.toLRSHom.toShHom q.toLRSHom.toShHom`
are equal by `rfl`: both are `CategoryTheory.Adjunction.leftAdjointCompIso` of a
pushforward-composition isomorphism, and the two pushforward-composition isomorphisms have
identity components, so structure eta identifies them. The same holds of the two spellings of
the comparison of Tag 01CD: `Stacks.RelativeVeryAmple.pullbackTensorModulesIso f A B` is
`Stacks.PullbackTensorCoherence.pullbackTensorComparison f.toLRSHom.toShHom A B` by `rfl`.
So `pullbackTensorComparison_comp`, which is stated for morphisms of ringed spaces, applies to
morphisms of schemes with no transport at all.

**The monoidal structure is `Stacks.AlgebraicGeometry.ThetaMul.schemeMonoidal`**, the structure
of [Stacks, Tag 01CA] on `X.Modules`, brought in as a local instance: an instance keyed on
`SheafOfModules (structureRingSheaf X.toRingedSpace)` is not tried against a goal keyed on
`X.Modules`, the two being equal only definitionally.

No Stacks tag is carried: none of the statements below is a clause of any tag.

## References

* [Stacks Project, Tag 01N8](https://stacks.math.columbia.edu/tag/01N8)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 01O7](https://stacks.math.columbia.edu/tag/01O7)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory AlgebraicGeometry
open Stacks.AlgebraicGeometry.MorphismsIntoProj (pullbackTwist toProj)
open Stacks.AlgebraicGeometry.ProjTwistTensorPowDegreeOpen (twist)
open Stacks.RelativeVeryAmple (tensorModules pullbackTensorModulesIso)
open AlgebraicGeometry.ProjectiveSpectrum.Proj (twistingSheaf)

universe v u

namespace Stacks.Monoidal

/-- **The square chase behind the multiplicativity of a contraction**, with every object and
morphism a variable.

Read `cab` and `cc` as the components of a contraction and `e` as its component on a tensor
product, `T₀` and `Tp` as the two tensorators, `wq` as the image of the inner tensorator, `mp`
and `mpq` as the two multiplications downstairs and `mu` as the multiplication upstairs. The
hypotheses are the compatibility of the contraction with the tensorators (`h1`), the
cancellation of the inner tensorator against its inverse (`h2`) and the naturality of the
contraction at the multiplication (`h3`); the conclusion is that the contraction intertwines the
two multiplications.

Nothing monoidal appears: the tensor products are opaque objects `P` and `Q` and the contraction
on them an arbitrary isomorphism, so the lemma is a statement of plain category theory and is
applied with `e` a `CategoryTheory.Iso.tensorIso`, whose `hom` and `inv` are the monoidal tensor
products of the components by definition. -/
theorem contractionMul_free {D : Type u} [Category.{v} D]
    {S SC R RC M P Q : D}
    (T₀ : S ≅ Q) (Tp : M ≅ P) (e : P ≅ Q)
    (cab : R ≅ S) (cc : RC ≅ SC)
    (wq : R ⟶ M) (mp : M ⟶ RC) (mpq : R ⟶ RC) (mu : S ⟶ SC)
    (h1 : cab.hom ≫ T₀.hom = wq ≫ Tp.hom ≫ e.hom)
    (h2 : wq ≫ mp = mpq)
    (h3 : mpq ≫ cc.hom = cab.hom ≫ mu) :
    T₀.inv ≫ mu ≫ cc.inv = e.inv ≫ Tp.inv ≫ mp := by
  have key : T₀.hom ≫ e.inv ≫ Tp.inv = cab.inv ≫ wq := by
    rw [Iso.eq_inv_comp, ← Category.assoc, h1]
    simp
  have h3' : mu ≫ cc.inv = cab.inv ≫ mpq := by
    rw [Iso.eq_inv_comp, ← Category.assoc, ← h3]
    simp
  rw [← cancel_epi T₀.hom, Iso.hom_inv_id_assoc, h3', ← h2, ← Category.assoc, ← key,
    Category.assoc, Category.assoc]

end Stacks.Monoidal

namespace Stacks.AlgebraicGeometry.PullbackTwistPower

attribute [local instance] Stacks.AlgebraicGeometry.ThetaMul.schemeMonoidal

/-! ### The composition law for pullback, in the scheme spelling -/

section Comp

variable {X Y Z : Scheme.{u}} (p : X ⟶ Y) (q : Y ⟶ Z)

/-- **The composition law for pullback of sheaves of modules on schemes is compatible with the
comparison of [Stacks, Tag 01CD].** This is
`Stacks.PullbackTensorCoherence.pullbackTensorComparison_comp`, which is stated for morphisms of
ringed spaces and for the comparison in the
`Stacks.PullbackTensorCoherence.pullbackTensorComparison` spelling, read at
`AlgebraicGeometry.Scheme.Modules.pullbackComp` and at
`Stacks.RelativeVeryAmple.pullbackTensorModulesIso`. No transport is needed: both pairs of
spellings agree by `rfl`. -/
theorem pullbackComp_tensorator (A B : Z.Modules) :
    (Scheme.Modules.pullbackComp p q).hom.app (A ⊗ B) ≫
        (pullbackTensorModulesIso (p ≫ q) A B).hom =
      (Scheme.Modules.pullback p).map (pullbackTensorModulesIso q A B).hom ≫
        (pullbackTensorModulesIso p ((Scheme.Modules.pullback q).obj A)
            ((Scheme.Modules.pullback q).obj B)).hom ≫
          ((Scheme.Modules.pullbackComp p q).hom.app A ⊗ₘ
            (Scheme.Modules.pullbackComp p q).hom.app B) :=
  Stacks.PullbackTensorCoherence.pullbackTensorComparison_comp
    p.toLRSHom.toShHom q.toLRSHom.toShHom A B

/-- **The composition law for pullback is multiplicative.** A morphism `u : A ⊗ B ⟶ C` of
`𝒪_Z`-modules induces a multiplication of the pullbacks along any morphism, by inverting the
comparison of [Stacks, Tag 01CD] and applying `u`. The composition law
`AlgebraicGeometry.Scheme.Modules.pullbackComp` carries the multiplication induced on the
pullbacks along `p ≫ q` to the one induced on the iterated pullbacks along `q` and then `p`.

No invertibility of `u` is assumed, so this applies to the multiplication of the twisting
sheaves of `Proj 𝒮` in every pair of degrees, not only in the degrees where it is an
isomorphism. -/
theorem pullbackComp_mul {A B C : Z.Modules} (u : A ⊗ B ⟶ C) :
    (pullbackTensorModulesIso (p ≫ q) A B).inv ≫
        (Scheme.Modules.pullback (p ≫ q)).map u ≫
          ((Scheme.Modules.pullbackComp p q).app C).inv =
      (((Scheme.Modules.pullbackComp p q).app A).inv ⊗ₘ
          ((Scheme.Modules.pullbackComp p q).app B).inv) ≫
        (pullbackTensorModulesIso p ((Scheme.Modules.pullback q).obj A)
            ((Scheme.Modules.pullback q).obj B)).inv ≫
          (Scheme.Modules.pullback p).map
            ((pullbackTensorModulesIso q A B).inv ≫ (Scheme.Modules.pullback q).map u) :=
  Stacks.Monoidal.contractionMul_free
    (pullbackTensorModulesIso (p ≫ q) A B)
    (pullbackTensorModulesIso p ((Scheme.Modules.pullback q).obj A)
      ((Scheme.Modules.pullback q).obj B))
    ((Scheme.Modules.pullbackComp p q).app A ⊗ᵢ (Scheme.Modules.pullbackComp p q).app B)
    ((Scheme.Modules.pullbackComp p q).app (A ⊗ B))
    ((Scheme.Modules.pullbackComp p q).app C)
    ((Scheme.Modules.pullback p).map (pullbackTensorModulesIso q A B).hom)
    ((Scheme.Modules.pullback p).map
      ((pullbackTensorModulesIso q A B).inv ≫ (Scheme.Modules.pullback q).map u))
    ((Scheme.Modules.pullback p).map ((Scheme.Modules.pullback q).map u))
    ((Scheme.Modules.pullback (p ≫ q)).map u)
    (pullbackComp_tensorator p q A B)
    (((Scheme.Modules.pullback p).map_comp (pullbackTensorModulesIso q A B).hom
          ((pullbackTensorModulesIso q A B).inv ≫
            (Scheme.Modules.pullback q).map u)).symm.trans
      (congrArg (Scheme.Modules.pullback p).map
        (Iso.hom_inv_id_assoc (pullbackTensorModulesIso q A B)
          ((Scheme.Modules.pullback q).map u))))
    ((Scheme.Modules.pullbackComp p q).hom.naturality u)

end Comp

/-! ### The contraction of the pullback along `Y ⟶ U_d ⟶ Proj 𝒮` -/

variable {S : Type u} {σ : Type u} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮] (d : ℕ)
  {Y : Scheme.{u}} (φ : Y ⟶ (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).toScheme)

/-- **The contraction of the pullback along `Y ⟶ U_d ⟶ Proj 𝒮` is multiplicative.** A morphism
`u : 𝒪(a) ⊗ 𝒪(b) ⟶ 𝒪(c)` of `𝒪_{Proj 𝒮}`-modules — the multiplication of the twisting sheaves
of [Stacks, Tag 01MQ] in the degrees `(a, b)` is one — induces a multiplication of the twists
pulled back along the composite `Y ⟶ U_d ⟶ Proj 𝒮`, and a multiplication of the pullbacks along
`φ` of the restricted twists, in each case by inverting the comparison of [Stacks, Tag 01CD] and
applying `u`. The contraction `pullbackTwistRestrictIso` carries the first to the second.

This is `Stacks.AlgebraicGeometry.PullbackTwistPower.pullbackComp_mul` at the factorisation
`toProj 𝒮 φ = φ ≫ (Proj.degreeOpen 𝒮 d).ι`, the contraction being the inverse of the component
of the composition law there by
`Stacks.AlgebraicGeometry.PullbackTwistPower.pullbackTwistRestrictIso_hom`. -/
theorem pullbackTwistRestrictIso_mul {A B C : (AlgebraicGeometry.Proj 𝒮).Modules}
    (u : A ⊗ B ⟶ C) :
    (pullbackTensorModulesIso (toProj 𝒮 φ) A B).inv ≫
        (Scheme.Modules.pullback (toProj 𝒮 φ)).map u ≫
          ((Scheme.Modules.pullbackComp φ
            (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).ι).app C).inv =
      (((Scheme.Modules.pullbackComp φ
              (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).ι).app A).inv ⊗ₘ
          ((Scheme.Modules.pullbackComp φ
            (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).ι).app B).inv) ≫
        (pullbackTensorModulesIso φ
            ((Scheme.Modules.pullback (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).ι).obj A)
            ((Scheme.Modules.pullback
              (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).ι).obj B)).inv ≫
          (Scheme.Modules.pullback φ).map
            ((pullbackTensorModulesIso (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).ι A B).inv ≫
              (Scheme.Modules.pullback (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).ι).map u) :=
  pullbackComp_mul φ (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).ι u

/-- **The contraction on the twists, at the multiplication of the twisting sheaves.** The
previous statement with `A`, `B` and `C` the twisting sheaves of degrees `a`, `b` and `a + b`,
so that the two multiplications are the ones the degreewise family of [Stacks, Tag 01O7] uses,
and with the contraction named. -/
theorem pullbackTwistRestrictIso_mul_twist (a b : ℤ)
    (u : tensorModules (AlgebraicGeometry.Proj 𝒮) (twistingSheaf 𝒮 a) (twistingSheaf 𝒮 b) ⟶
      twistingSheaf 𝒮 (a + b)) :
    (pullbackTensorModulesIso (toProj 𝒮 φ) (twistingSheaf 𝒮 a) (twistingSheaf 𝒮 b)).inv ≫
        (Scheme.Modules.pullback (toProj 𝒮 φ)).map u ≫
          (pullbackTwistRestrictIso 𝒮 d φ (a + b)).hom =
      ((pullbackTwistRestrictIso 𝒮 d φ a).hom ⊗ₘ (pullbackTwistRestrictIso 𝒮 d φ b).hom) ≫
        (pullbackTensorModulesIso φ (twist 𝒮 d a) (twist 𝒮 d b)).inv ≫
          (Scheme.Modules.pullback φ).map
            ((pullbackTensorModulesIso (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).ι
                (twistingSheaf 𝒮 a) (twistingSheaf 𝒮 b)).inv ≫
              (Scheme.Modules.pullback (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).ι).map u) :=
  pullbackTwistRestrictIso_mul 𝒮 d φ u

end Stacks.AlgebraicGeometry.PullbackTwistPower

end
