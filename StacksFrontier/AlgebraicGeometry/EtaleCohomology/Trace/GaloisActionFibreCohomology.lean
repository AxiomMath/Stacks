module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkOfDerivedPushforward
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ArithmeticFrobeniusInverse
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricFrobeniusStalk
public import StacksCore.Tactic.StacksAttribute

/-!
# The Galois action on the stalk of a direct image and on the geometric fibre

Let `k` be a field, let `K` be an algebraically closed extension of `k` and let `α : X ⟶ Spec k`
be a scheme over `k`.  The structure morphism `Spec K ⟶ Spec k` is a geometric point of
`Spec k`, and the geometric fibre of `α` at it is the base change `X_K = X ×_{Spec k} Spec K`.
An element `σ` of `G_k = Gal(K/k)` is an endomorphism of that geometric point, so it acts on the
stalk there of every abelian étale sheaf — the action of Étale Cohomology Section 03QW — and it
acts on `X_K` by `id_X × Spec σ`.

For an abelian sheaf `ℱ` on the small étale site of `X`, the germ at the geometric point of a
section of `α_* ℱ` over an étale neighbourhood `W` of `Spec K` is a section of `ℱ` over
`X_W = X ×_{Spec k} W`, and the chosen lift of the geometric point to `W` induces a morphism
`X_K ⟶ X_W` over `X` along which that section restricts to a section of `ℱ|_{X_K}`.  This is the
comparison of Étale Cohomology, Theorem 03Q9 in degree zero.  The main result is that it carries
the Galois action on the stalk to restriction along `id_X × Spec σ`: translating the lift by `σ`
precomposes the morphism `X_K ⟶ X_W` with `id_X × Spec σ`.

## Main definitions

* `Stacks.Frobenius.galoisHigherDirectImageStalkAction` — the action of `σ` on the functor
  `ℱ ↦ (R^j α_* ℱ)_{Spec K}`, and
  `Stacks.Frobenius.galoisHigherDirectImageStalkDistribMulAction` — that action as a
  `G_k`-module structure on the stalk of a single sheaf.
* `Stacks.Frobenius.galoisLift` — the translate by `σ` of a lift of the geometric point to an
  étale neighbourhood.
* `Stacks.Frobenius.fibreLift` — the morphism `X_K ⟶ X_W` over `X` induced by such a lift.
* `Stacks.Frobenius.fibreGerm` and `Stacks.Frobenius.fibreComparison` — restriction of a section
  over `X_W` to the geometric fibre, and the resulting map from the stalk of `α_* ℱ`.

## Main results

* `Stacks.Frobenius.galoisBaseChange_one` and `Stacks.Frobenius.galoisBaseChange_mul` — the
  automorphisms `id_X × Spec σ` of `X_K` compose contravariantly, so inverse image along them is
  a left action of `G_k`.
* `Stacks.Frobenius.galoisHigherDirectImageStalkAction_one` and
  `Stacks.Frobenius.galoisHigherDirectImageStalkAction_mul` — the action on the stalk of a
  higher direct image is a left action of `G_k`.
* `Stacks.Frobenius.galoisBaseChange_comp_fibreLift` — translating the lift by `σ` precomposes
  `X_K ⟶ X_W` with `id_X × Spec σ`.
* `Stacks.Frobenius.fibreComparison_galoisStalkAction` — the comparison carries the Galois
  action on the stalk to restriction along `id_X × Spec σ`.

## Implementation notes

The Galois action on the stalk is not assumed: it is
`Stacks.Frobenius.galoisStalkAction` at the geometric point `Spec K ⟶ Spec k`, viewed as
`rationalGeometricPoint K (𝟙 (Spec k))`, whose `hom` is `specAlgebraMap k K` by definition.  That
action is Étale Cohomology Section 03QW — `σ` as an endomorphism of the geometric point, through
Tag 04FN, acting on the fiber functor of the associated point of the small étale site — and
`galoisStalkAction_one` and `galoisStalkAction_mul` already make it a left action, so the
`G_k`-module structure below is obtained by whiskering and needs no new input.

The geometric fibre `AlgebraicGeometry.geometricFibre α (rationalGeometricPoint K (𝟙 _))` and the
base change `Stacks.Frobenius.fieldBaseChange X K` are the same scheme by definition, which is
`geometricFibre_eq_fieldBaseChange`; so the automorphism `galoisBaseChange X K σ` of the latter
is an automorphism of the geometric fibre, and the two Galois actions are the stalk and the base
change of one endomorphism of the geometric point
(`galoisBaseChange_comp_geometricFibreToPoint`).

The comparison is built germwise from `Stacks.EtaleCohomology.smallEtaleSectionsPullbackAb`, so
no isomorphism is inverted and nothing is assumed of `α`, of `ℱ` or of `K/k` beyond algebraic
closedness of `K`.  Equivariance is stated on the germ at an arbitrary étale neighbourhood; since
the germs are jointly surjective onto the stalk
(`CategoryTheory.GrothendieckTopology.Point.presheafFiber_hom_ext`), this determines the induced
map on the whole stalk.

### No unrestricted `@[stacks 03ST]`

Tag 03ST has two assertions: that the identification of Étale Cohomology, Theorem 03Q9 between
`(R^j α_* ℱ)_{Spec k̄}` and `H^j(X_{k̄}, ℱ|_{X_{k̄}})` exists and is an isomorphism, and that it is
`G_k`-equivariant.  Only the second is proved here, and only in degree zero; the tag attribute
below carries both qualifications.

The first assertion is Tag 03Q9, which this library has only over a strictly henselian base
(`Stacks.StrictlyHenselian.higherDirectImageEtaleStalkIso`); the general case needs Tag 03Q6,
which is absent.  The equivariance in degree `j > 0` needs the degree-`j` form of the comparison
together with a composition law for restriction of sections along a composite of morphisms of
schemes — transitivity of `Stacks.EtaleCohomology.smallEtaleSectionsPullbackAb` in the scheme
over the base, rather than in the étale object, which
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/LocalAcyclicity/SpecializationMap.lean` does not
provide.  Neither is assumed below.

## References

* [Stacks Project, Tag 03ST](https://stacks.math.columbia.edu/tag/03ST)
* [Stacks Project, Tag 03QW](https://stacks.math.columbia.edu/tag/03QW)
* [Stacks Project, Tag 03Q9](https://stacks.math.columbia.edu/tag/03Q9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.EtaleCohomology

universe u

namespace Stacks.Frobenius

section GaloisFibre

variable {k : Type u} [Field k] (X : Over (Spec (.of k))) (K : Type u) [Field K] [Algebra k K]

/-- The Galois automorphism of `X_K` attached to the identity is the identity. -/
@[simp]
public lemma galoisBaseChange_one : galoisBaseChange X K (1 : K ≃ₐ[k] K) = 𝟙 _ := by
  refine pullback.hom_ext ?_ ?_
  · rw [galoisBaseChange_comp_fst, Category.id_comp]
  · rw [galoisBaseChange_comp_snd, Category.id_comp,
      show CommRingCat.ofHom (AlgEquiv.toAlgHom (1 : K ≃ₐ[k] K)).toRingHom =
        𝟙 (CommRingCat.of K) from rfl, Spec.map_id, Category.comp_id]

/-- The Galois automorphisms of `X_K` compose contravariantly: `id_X × Spec(στ)` is
`id_X × Spec σ` followed by `id_X × Spec τ`, because `Spec` is contravariant.  Inverse image
along them is therefore a left action of `G_k`. -/
@[sga "7 XIII 1.1.1" "partial"]
public lemma galoisBaseChange_mul (σ τ : K ≃ₐ[k] K) :
    galoisBaseChange X K (σ * τ) = galoisBaseChange X K σ ≫ galoisBaseChange X K τ := by
  refine pullback.hom_ext ?_ ?_
  · rw [galoisBaseChange_comp_fst, Category.assoc, galoisBaseChange_comp_fst,
      galoisBaseChange_comp_fst]
  · rw [galoisBaseChange_comp_snd, Category.assoc, galoisBaseChange_comp_snd,
      galoisBaseChange_comp_snd_assoc, ← Spec.map_comp]
    rfl

end GaloisFibre

section StalkAction

variable {k : Type u} [Field k] (K : Type u) [Field K] [IsAlgClosed K] [Algebra k K]
  (X : Over (Spec (.of k))) (j : ℕ)

/-- **The Galois action on the stalk of a higher direct image, Étale Cohomology Section
03QW.** The action of `σ ∈ G_k` on the functor `ℱ ↦ (R^j α_* ℱ)_{Spec K}` sending an abelian
sheaf on the small étale site of `X` to the stalk at the geometric point `Spec K ⟶ Spec k` of
the `j`-th higher direct image along `α`.

It is the action on the stalk functor of `Stacks.Frobenius.galoisStalkAction`, whiskered with
the higher direct image; so it is the action which moves the geometric lift of a germ, and it
does not depend on `α` or on `j`. -/
public def galoisHigherDirectImageStalkAction (σ : K ≃ₐ[k] K) :
    (smallEtalePushforwardAb X.hom).rightDerived j ⋙
        smallEtaleStalkAb (specAlgebraMap k K) ⟶
      (smallEtalePushforwardAb X.hom).rightDerived j ⋙
        smallEtaleStalkAb (specAlgebraMap k K) :=
  Functor.whiskerLeft ((smallEtalePushforwardAb X.hom).rightDerived j)
    (galoisStalkAction Ab.{u + 1} K σ (𝟙 (Spec (.of k))))

/-- The identity acts as the identity on the stalk of the higher direct image. -/
@[simp]
public lemma galoisHigherDirectImageStalkAction_one :
    galoisHigherDirectImageStalkAction K X j (1 : K ≃ₐ[k] K) = 𝟙 _ := by
  rw [galoisHigherDirectImageStalkAction, galoisStalkAction_one]
  exact Functor.whiskerLeft_id' _

/-- The Galois group acts on the left on the stalk of the higher direct image. -/
public lemma galoisHigherDirectImageStalkAction_mul (σ τ : K ≃ₐ[k] K) :
    galoisHigherDirectImageStalkAction K X j (σ * τ) =
      galoisHigherDirectImageStalkAction K X j τ ≫
        galoisHigherDirectImageStalkAction K X j σ := by
  rw [galoisHigherDirectImageStalkAction, galoisHigherDirectImageStalkAction,
    galoisHigherDirectImageStalkAction, galoisStalkAction_mul]
  rfl

variable (F : Sheaf (smallEtaleTopology X.left) Ab.{u + 1})

/-- The identity acts as the identity on the stalk of `R^j α_* ℱ`. -/
@[simp]
public lemma galoisHigherDirectImageStalkAction_one_app :
    (galoisHigherDirectImageStalkAction K X j (1 : K ≃ₐ[k] K)).app F = 𝟙 _ := by
  rw [galoisHigherDirectImageStalkAction_one]
  rfl

/-- The Galois group acts on the left on the stalk of `R^j α_* ℱ`. -/
public lemma galoisHigherDirectImageStalkAction_mul_app (σ τ : K ≃ₐ[k] K) :
    (galoisHigherDirectImageStalkAction K X j (σ * τ)).app F =
      (galoisHigherDirectImageStalkAction K X j τ).app F ≫
        (galoisHigherDirectImageStalkAction K X j σ).app F := by
  rw [galoisHigherDirectImageStalkAction_mul]
  rfl

/-- **The stalk of a higher direct image as a `G_k`-module.** The absolute Galois group acts on
the stalk at `Spec K` of `R^j α_* ℱ` by the action of Étale Cohomology Section 03QW, each `σ`
acting by a morphism of abelian groups. -/
@[instance_reducible]
public def galoisHigherDirectImageStalkDistribMulAction :
    DistribMulAction (K ≃ₐ[k] K)
      (((smallEtalePushforwardAb X.hom).rightDerived j ⋙
        smallEtaleStalkAb (specAlgebraMap k K)).obj F) where
  smul σ x := ConcreteCategory.hom ((galoisHigherDirectImageStalkAction K X j σ).app F) x
  one_smul x :=
    ConcreteCategory.congr_hom (galoisHigherDirectImageStalkAction_one_app K X j F) x
  mul_smul σ τ x :=
    ConcreteCategory.congr_hom
      (galoisHigherDirectImageStalkAction_mul_app K X j F σ τ) x
  smul_zero σ := map_zero ((galoisHigherDirectImageStalkAction K X j σ).app F).hom
  smul_add σ x y := map_add ((galoisHigherDirectImageStalkAction K X j σ).app F).hom x y

/-- The geometric fibre of `α : X ⟶ Spec k` at the geometric point `Spec K ⟶ Spec k` is the
base change `X_K`. -/
public lemma geometricFibre_eq_fieldBaseChange :
    geometricFibre X.hom (rationalGeometricPoint K (𝟙 (Spec (.of k)))) =
      fieldBaseChange X K :=
  rfl

/-- **The two Galois actions come from one endomorphism of the geometric point.** The Galois
automorphism `id_X × Spec σ` of the geometric fibre `X_K` lies over the endomorphism `Spec σ` of
the geometric point `Spec K ⟶ Spec k` which induces the action of Étale Cohomology Section
03QW on étale stalks. -/
public lemma galoisBaseChange_comp_geometricFibreToPoint (σ : K ≃ₐ[k] K) :
    galoisBaseChange X K σ ≫
        geometricFibreToPoint X.hom (rationalGeometricPoint K (𝟙 (Spec (.of k)))) =
      geometricFibreToPoint X.hom (rationalGeometricPoint K (𝟙 (Spec (.of k)))) ≫
        (galoisPointHom K σ (𝟙 (Spec (.of k)))).hom :=
  galoisBaseChange_comp_snd X K σ

end StalkAction

section FibreComparison

variable {k : Type u} [Field k] (K : Type u) [Field K] [IsAlgClosed K] [Algebra k K]
  (X : Over (Spec (.of k)))

/-- **The translate by `σ` of a lift of the geometric point.** An element `σ` of `G_k` is an
endomorphism of the geometric point `Spec K ⟶ Spec k`, so it moves a lift of that point to an
étale neighbourhood `W` of `Spec k` by precomposition with `Spec σ`.  This is the action on
lifts underlying the stalk action of Étale Cohomology Section 03QW. -/
public def galoisLift (σ : K ≃ₐ[k] K) (W : (Spec (.of k)).Etale)
    (u : (Scheme.pointSmallEtale (specAlgebraMap k K)).fiber.obj W) :
    (Scheme.pointSmallEtale (specAlgebraMap k K)).fiber.obj W :=
  (smallEtalePointHom (Spec (.of k)) (galoisPointHom K σ (𝟙 (Spec (.of k))))).hom.app W u

/-- The translated lift is the given one precomposed with `Spec σ`. -/
@[simp]
public lemma galoisLift_left (σ : K ≃ₐ[k] K) (W : (Spec (.of k)).Etale)
    (u : (Scheme.pointSmallEtale (specAlgebraMap k K)).fiber.obj W) :
    (galoisLift K σ W u).left =
      Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) ≫ u.left :=
  rfl

/-- **The geometric fibre over an étale neighbourhood of the geometric point.** A lift `u` of
the geometric point `Spec K ⟶ Spec k` to an étale neighbourhood `W` induces a morphism
`X_K ⟶ X_W = X ×_{Spec k} W` over `X`, along which sections of a sheaf on `X_W` restrict to the
geometric fibre. -/
public def fibreLift (W : (Spec (.of k)).Etale)
    (u : (Scheme.pointSmallEtale (specAlgebraMap k K)).fiber.obj W) :
    fieldBaseChange X K ⟶ ((smallEtaleBaseChange X.hom).obj W).left :=
  pullback.lift (pullback.snd X.hom (specAlgebraMap k K) ≫ u.left)
    (pullback.fst X.hom (specAlgebraMap k K))
    ((Category.assoc _ _ _).trans
      ((congrArg (fun z => pullback.snd X.hom (specAlgebraMap k K) ≫ z) (Over.w u)).trans
        pullback.condition.symm))

/-- The morphism `X_K ⟶ X_W` lies over `X`. -/
public lemma fibreLift_comp_hom (W : (Spec (.of k)).Etale)
    (u : (Scheme.pointSmallEtale (specAlgebraMap k K)).fiber.obj W) :
    fibreLift K X W u ≫ ((smallEtaleBaseChange X.hom).obj W).hom =
      pullback.fst X.hom (specAlgebraMap k K) :=
  pullback.lift_snd _ _ _

/-- The first projection of `X_K ⟶ X_W` is the given lift composed with the projection to `K`. -/
private theorem fibreLift_comp_fst (W : (Spec (.of k)).Etale)
    (u : (Scheme.pointSmallEtale (specAlgebraMap k K)).fiber.obj W) :
    fibreLift K X W u ≫ pullback.fst W.hom X.hom =
      pullback.snd X.hom (specAlgebraMap k K) ≫ u.left :=
  pullback.lift_fst _ _ _

/-- The second projection of `X_K ⟶ X_W` is the projection to `X`. -/
private theorem fibreLift_comp_snd (W : (Spec (.of k)).Etale)
    (u : (Scheme.pointSmallEtale (specAlgebraMap k K)).fiber.obj W) :
    fibreLift K X W u ≫ pullback.snd W.hom X.hom = pullback.fst X.hom (specAlgebraMap k K) :=
  pullback.lift_snd _ _ _

/-- The morphism `X_K ⟶ X_W` is natural in the étale neighbourhood of the geometric point. -/
public lemma fibreLift_comp_map (W W' : (Spec (.of k)).Etale) (m : W ⟶ W')
    (u : (Scheme.pointSmallEtale (specAlgebraMap k K)).fiber.obj W) :
    fibreLift K X W u ≫ ((smallEtaleBaseChange X.hom).map m).left =
      fibreLift K X W' ((Scheme.pointSmallEtale (specAlgebraMap k K)).fiber.map m u) := by
  refine pullback.hom_ext ?_ ?_
  · erw [Category.assoc, pullback.lift_fst, ← Category.assoc, fibreLift_comp_fst,
      fibreLift_comp_fst, Category.assoc]
  · erw [Category.assoc, pullback.lift_snd, fibreLift_comp_snd, fibreLift_comp_snd]

/-- **Translating the lift by `σ` precomposes `X_K ⟶ X_W` with `id_X × Spec σ`.** This is the
geometric content of the equivariance of the comparison with the cohomology of the geometric
fibre: the Galois action on lifts of the geometric point and the Galois action on `X_K` are the
same automorphism seen on the two sides. -/
public lemma galoisBaseChange_comp_fibreLift (σ : K ≃ₐ[k] K) (W : (Spec (.of k)).Etale)
    (u : (Scheme.pointSmallEtale (specAlgebraMap k K)).fiber.obj W) :
    fibreLift K X W (galoisLift K σ W u) =
      galoisBaseChange X K σ ≫ fibreLift K X W u := by
  refine pullback.hom_ext ?_ ?_
  · erw [Category.assoc, fibreLift_comp_fst, fibreLift_comp_fst, galoisLift_left,
      galoisBaseChange_comp_snd_assoc]
    rfl
  · refine (fibreLift_comp_snd K X W _).trans ?_
    refine ((galoisBaseChange_comp_fst X K σ).symm.trans ?_)
    exact (congrArg (galoisBaseChange X K σ ≫ ·) (fibreLift_comp_snd K X W u)).symm.trans
      (Category.assoc _ _ _).symm

variable (F : Sheaf (smallEtaleTopology X.left) Ab.{u + 1})

/-- **Restriction of a section to the geometric fibre.** A section of `α_* ℱ` over an étale
neighbourhood `W` of the geometric point is a section of `ℱ` over `X_W`; restricting it along
`X_K ⟶ X_W` gives a global section of `ℱ|_{X_K}`. -/
public def fibreGerm (W : (Spec (.of k)).Etale)
    (u : (Scheme.pointSmallEtale (specAlgebraMap k K)).fiber.obj W) :
    ((smallEtalePushforwardAb X.hom).obj F).obj.obj (op W) ⟶
      (Sheaf.Γ (smallEtaleTopology (fieldBaseChange X K)) Ab.{u + 1}).obj
        ((smallEtalePullbackAb (pullback.fst X.hom (specAlgebraMap k K))).obj F) :=
  (smallEtaleSectionsPullbackAb (pullback.fst X.hom (specAlgebraMap k K))
    ((smallEtaleBaseChange X.hom).obj W) (fibreLift K X W u)
    (fibreLift_comp_hom K X W u)).app F

/-- **The comparison of Étale Cohomology, Theorem 03Q9 in degree zero.** The stalk at the
geometric point `Spec K ⟶ Spec k` of the direct image `α_* ℱ` maps to the global sections of
`ℱ|_{X_K}` on the geometric fibre, by restricting the germ of a section over an étale
neighbourhood along the induced morphism `X_K ⟶ X_W`. -/
public def fibreComparison :
    (smallEtaleStalkAb (specAlgebraMap k K)).obj ((smallEtalePushforwardAb X.hom).obj F) ⟶
      (Sheaf.Γ (smallEtaleTopology (fieldBaseChange X K)) Ab.{u + 1}).obj
        ((smallEtalePullbackAb (pullback.fst X.hom (specAlgebraMap k K))).obj F) :=
  (Scheme.pointSmallEtale (specAlgebraMap k K)).presheafFiberDesc
    (P := (sheafToPresheaf _ _).obj ((smallEtalePushforwardAb X.hom).obj F))
    (fun W u => fibreGerm K X F W u)
    (fun {W W'} m u => by
      have hrm : (fibreLift K X W u ≫ ((smallEtaleBaseChange X.hom).map m).left) ≫
          ((smallEtaleBaseChange X.hom).obj W').hom =
            pullback.fst X.hom (specAlgebraMap k K) :=
        (congrArg (fun z => z ≫ ((smallEtaleBaseChange X.hom).obj W').hom)
          (fibreLift_comp_map K X W W' m u)).trans (fibreLift_comp_hom K X W' _)
      have h1 := map_comp_smallEtaleSectionsPullbackAb
        (pullback.fst X.hom (specAlgebraMap k K))
        ((smallEtaleBaseChange X.hom).obj W) (fibreLift K X W u)
        ((smallEtaleBaseChange X.hom).map m) (fibreLift_comp_hom K X W u) hrm
      have h2 := smallEtaleSectionsPullbackAb_congr
        (pullback.fst X.hom (specAlgebraMap k K))
        ((smallEtaleBaseChange X.hom).obj W') _ hrm
        (fibreLift_comp_hom K X W'
          ((Scheme.pointSmallEtale (specAlgebraMap k K)).fiber.map m u))
        (fibreLift_comp_map K X W W' m u)
      exact congrArg (fun φ => NatTrans.app φ F) (h1.trans h2))

/-- On the germ at an étale neighbourhood of the geometric point, the comparison is restriction
to the geometric fibre. -/
@[reassoc]
public lemma toPresheafFiber_comp_fibreComparison (W : (Spec (.of k)).Etale)
    (u : (Scheme.pointSmallEtale (specAlgebraMap k K)).fiber.obj W) :
    (Scheme.pointSmallEtale (specAlgebraMap k K)).toPresheafFiber W u
          ((sheafToPresheaf _ _).obj ((smallEtalePushforwardAb X.hom).obj F)) ≫
        fibreComparison K X F =
      fibreGerm K X F W u :=
  (Scheme.pointSmallEtale (specAlgebraMap k K)).toPresheafFiber_presheafFiberDesc _ _ W u

/-- The Galois action of Étale Cohomology Section 03QW carries the germ at a lift of the
geometric point to the germ at the translate of that lift by `σ`. -/
@[reassoc]
public lemma toPresheafFiber_comp_galoisStalkAction (σ : K ≃ₐ[k] K)
    (W : (Spec (.of k)).Etale)
    (u : (Scheme.pointSmallEtale (specAlgebraMap k K)).fiber.obj W) :
    (Scheme.pointSmallEtale (specAlgebraMap k K)).toPresheafFiber W u
          ((sheafToPresheaf _ _).obj ((smallEtalePushforwardAb X.hom).obj F)) ≫
        (galoisStalkAction Ab.{u + 1} K σ (𝟙 (Spec (.of k)))).app
          ((smallEtalePushforwardAb X.hom).obj F) =
      (Scheme.pointSmallEtale (specAlgebraMap k K)).toPresheafFiber W (galoisLift K σ W u)
        ((sheafToPresheaf _ _).obj ((smallEtalePushforwardAb X.hom).obj F)) := by
  dsimp only [galoisStalkAction, GrothendieckTopology.Point.Hom.sheafFiber,
    Functor.whiskerLeft_app]
  exact (Scheme.pointSmallEtale (specAlgebraMap k K)).toPresheafFiber_presheafFiberDesc
    (A := Ab.{u + 1}) _ _ W u

/-- **Stacks Project, Tag 03ST, Galois equivariance in degree zero.** The comparison of Étale
Cohomology, Theorem 03Q9 carries the Galois action of Étale Cohomology Section 03QW on the stalk
`(α_* ℱ)_{Spec k̄}` to restriction along the automorphism `id_X × Spec σ` of the geometric fibre
`X_{k̄}`: on the germ at an étale neighbourhood `W` of the geometric point, acting by `σ` and
then comparing is restricting along `(id_X × Spec σ) ∘ (X_{k̄} ⟶ X_W)`.

Since the germs are jointly surjective onto the stalk, this determines the induced map on the
whole stalk, and it is the statement that the identification of Tag 03Q9 is a map of
`G_k`-modules. -/
@[stacks 03ST "Galois equivariance of the Theorem 03Q9 comparison in degree zero: \
unconditional in `α`, in the sheaf and in the algebraically closed extension, stated on the \
germ at an arbitrary étale neighbourhood of the geometric point. That the comparison is an \
isomorphism is Tag 03Q9, available in this library only over a strictly henselian base, and \
the equivariance in degree j > 0 needs transitivity of restriction of sections in the scheme \
over the base; neither is assumed here"]
public theorem fibreComparison_galoisStalkAction (σ : K ≃ₐ[k] K)
    (W : (Spec (.of k)).Etale)
    (u : (Scheme.pointSmallEtale (specAlgebraMap k K)).fiber.obj W) :
    (Scheme.pointSmallEtale (specAlgebraMap k K)).toPresheafFiber W u
          ((sheafToPresheaf _ _).obj ((smallEtalePushforwardAb X.hom).obj F)) ≫
        (galoisStalkAction Ab.{u + 1} K σ (𝟙 (Spec (.of k)))).app
          ((smallEtalePushforwardAb X.hom).obj F) ≫
        fibreComparison K X F =
      (smallEtaleSectionsPullbackAb (pullback.fst X.hom (specAlgebraMap k K))
        ((smallEtaleBaseChange X.hom).obj W)
        (galoisBaseChange X K σ ≫ fibreLift K X W u)
        ((congrArg (fun z => z ≫ ((smallEtaleBaseChange X.hom).obj W).hom)
            (galoisBaseChange_comp_fibreLift K X σ W u).symm).trans
          (fibreLift_comp_hom K X W (galoisLift K σ W u)))).app F := by
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun z => z ≫ fibreComparison K X F)
    (toPresheafFiber_comp_galoisStalkAction K X F σ W u)).trans ?_
  refine (toPresheafFiber_comp_fibreComparison K X F W (galoisLift K σ W u)).trans ?_
  exact congrArg (fun φ => NatTrans.app φ F)
    (smallEtaleSectionsPullbackAb_congr _ _ _ _ _
      (galoisBaseChange_comp_fibreLift K X σ W u))

end FibreComparison

end Stacks.Frobenius

end
