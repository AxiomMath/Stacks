module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.AdicThickeningEquivalence
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.AdicThickeningPushforwardSystem

/-!
# The completion functor on adic thickenings is an equivalence

Let `A` be Noetherian and `I`-adically complete, and let `f : X ⟶ Spec A` be separated, locally
of finite type and quasi-compact. The functor
`AlgebraicGeometry.adicThickeningCompletionFunctor A I f` sends a coherent `𝒪_X`-module with
support proper over `A` to the system `(ℱ|_{Xₙ})` of its restrictions to the adic thickenings.
This file proves that this functor is essentially surjective, and hence an equivalence of
categories.

## Main definitions

* `AlgebraicGeometry.adicThickeningEssSurjSystemIso`: the isomorphism of systems on the
  thickenings attached to a degreewise comparison on `X` compatible with the transitions.

## Main results

* `AlgebraicGeometry.adicThickeningEssSurjIso_comm`: the comparisons
  `AlgebraicGeometry.adicThickeningEssSurjIso` commute with the transition isomorphisms.
* `AlgebraicGeometry.essSurj_adicThickeningCompletionFunctor`: the completion functor is
  essentially surjective.
* `AlgebraicGeometry.isEquivalence_adicThickeningCompletionFunctor`: the completion functor is an
  equivalence of categories.

## References

* [Stacks Project, Tag 088F](https://stacks.math.columbia.edu/tag/088F)
* [Stacks Project, Tag 088E](https://stacks.math.columbia.edu/tag/088E)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
* [Stacks Project, Tag 0EL1](https://stacks.math.columbia.edu/tag/0EL1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.FormalFunctions (baseIdealSheaf)

universe u

namespace AlgebraicGeometry

open Stacks.Algebraization
open Stacks.Descent (pushUnit pullbackCompHom)

/-! ### Inverting a commuting square -/

/-- **A commuting square of isomorphisms commutes with the inverses.** For isomorphisms `e₁` and
`e₀`, the square `e₁.hom ≫ a = b ≫ e₀.hom` gives the square `e₁.inv ≫ b = a ≫ e₀.inv`. -/
public theorem inv_comp_eq_comp_inv_of_comm {C : Type*} [Category C] {P₁ P₀ Q₁ Q₀ : C}
    (e₁ : P₁ ≅ Q₁) (e₀ : P₀ ≅ Q₀) {a : Q₁ ⟶ Q₀} {b : P₁ ⟶ P₀}
    (hcomm : e₁.hom ≫ a = b ≫ e₀.hom) :
    e₁.inv ≫ b = a ≫ e₀.inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, hcomm, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

/-- If `u₁ = cp₁ ≫ p₁.hom`, `u₀ = cp₀ ≫ p₀.hom`, `m₁ = p₁.inv ≫ b₁`, `m₀ = p₀.inv ≫ b₀`,
`tr ≫ b₀ = b₁ ≫ T` and `cp₁ ≫ tr = cp₀`, then `u₁ ≫ m₁ ≫ T = u₀ ≫ m₀`. -/
private theorem unit_comp_map_comp_eq_of_projection {C : Type*} [Category C]
    {M C₁ C₀ D₁ D₀ N₁ N₀ : C} (p₁ : C₁ ≅ D₁) (p₀ : C₀ ≅ D₀)
    {cp₁ : M ⟶ C₁} {cp₀ : M ⟶ C₀} {tr : C₁ ⟶ C₀} {b₁ : C₁ ⟶ N₁} {b₀ : C₀ ⟶ N₀}
    {T : N₁ ⟶ N₀} {u₁ : M ⟶ D₁} {u₀ : M ⟶ D₀} {m₁ : D₁ ⟶ N₁} {m₀ : D₀ ⟶ N₀}
    (hu₁ : cp₁ ≫ p₁.hom = u₁) (hu₀ : cp₀ ≫ p₀.hom = u₀)
    (hm₁ : m₁ = p₁.inv ≫ b₁) (hm₀ : m₀ = p₀.inv ≫ b₀)
    (hb : tr ≫ b₀ = b₁ ≫ T) (hcp : cp₁ ≫ tr = cp₀) :
    u₁ ≫ m₁ ≫ T = u₀ ≫ m₀ := by
  rw [← hu₁, ← hu₀, hm₁, hm₀]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← hb, ← Category.assoc, hcp]

/-! ### The degreewise comparison and its transition square -/

section Compare

variable (A : Type u) [CommRing A] (I : Ideal A) {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
  [IsLocallyNoetherian X] [LocallyOfFiniteType f]
  (P : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
  (S : AdicCoherentModuleSystem A I f)
  (β : ∀ n : ℕ, ((completionFunctor X (baseIdealSheaf A I f)).obj P).obj.obj (op n) ≅
    adicPushforwardObj A I f S n)

/-- The comparison on the `n`-th thickening attached to a degreewise comparison on `X`. -/
public def adicThickeningEssSurjIso (n : ℕ) :
    adicThickeningCompletion A I f P.obj n ≅ S.obj n :=
  adicThickeningCompletion_iso_of_pushforward_iso A I f n
    (G := adicThickeningCompletion A I f P.obj n) (H := S.obj n)
    ((adicThickeningCompletionPushforwardIso A I f P n).symm ≪≫ β n)

/-- The direct image of `AlgebraicGeometry.adicThickeningEssSurjIso` along `Xₙ ⟶ X` is the
given comparison `β n`, composed with the inverse of
`AlgebraicGeometry.adicThickeningCompletionPushforwardIso`. -/
public theorem map_adicThickeningEssSurjIso (n : ℕ) :
    (Scheme.Modules.pushforward (pullback.fst f (adicThickeningι A I n))).map
        (adicThickeningEssSurjIso A I f P S β n).hom =
      (adicThickeningCompletionPushforwardIso A I f P n).inv ≫ (β n).hom :=
  (Stacks.ClosedImmersion.fullyFaithfulPushforward
    (pullback.fst f (adicThickeningι A I n))).map_preimage _

/-- The comparisons `AlgebraicGeometry.adicThickeningEssSurjIso` commute with the transition
isomorphisms of the two systems. -/
public theorem adicThickeningEssSurjIso_comm
    (hβ : ∀ n : ℕ, ((completionFunctor X (baseIdealSheaf A I f)).obj P).obj.map
          (homOfLE (Nat.le_succ n)).op ≫ (β n).hom =
        (β (n + 1)).hom ≫ adicPushforwardTransition A I f S n)
    (n : ℕ) :
    (Scheme.Modules.pullback (adicBaseChangeSucc A I f n)).map
          (adicThickeningEssSurjIso A I f P S β (n + 1)).hom ≫ (S.transitionIso n).hom =
      (adicThickeningCompletionTransition A I f P.obj n).hom ≫
        (adicThickeningEssSurjIso A I f P S β n).hom := by
  refine pullback_map_comp_eq_of_unit_comp (pullback.fst f (adicThickeningι A I (n + 1)))
    (adicBaseChangeSucc A I f n) (adicBaseChangeSucc_fst A I f n)
    (Stacks.ClosedImmersion.fullyFaithfulPushforward
      (pullback.fst f (adicThickeningι A I n))).faithful
    P.obj (S.obj (n + 1)) (S.obj n) (S.transitionIso n).hom
    (adicThickeningEssSurjIso A I f P S β (n + 1)).hom
    (adicThickeningEssSurjIso A I f P S β n).hom
    (Θ := (adicThickeningCompletionTransition A I f P.obj n).hom)
    (T := adicPushforwardTransition A I f S n)
    (show (adicThickeningCompletionTransition A I f P.obj n).hom =
        pullbackCompHom (adicBaseChangeSucc A I f n)
          (pullback.fst f (adicThickeningι A I (n + 1)))
          (pullback.fst f (adicThickeningι A I n)) (adicBaseChangeSucc_fst A I f n) P.obj from
      (pullbackComp_pullbackCongr_app_eq_adicThickeningCompletionTransition A I f n P.obj).symm)
    rfl (epi_unit_app_adicThickeningCompletion A I f P n) ?_
  exact unit_comp_map_comp_eq_of_projection (C := X.Modules)
    (adicThickeningCompletionPushforwardIso A I f P (n + 1))
    (adicThickeningCompletionPushforwardIso A I f P n)
    (adicThickeningCompletionPushforwardIso_projection A I f P (n + 1))
    (adicThickeningCompletionPushforwardIso_projection A I f P n)
    (map_adicThickeningEssSurjIso A I f P S β (n + 1))
    (map_adicThickeningEssSurjIso A I f P S β n)
    (hβ n) (completionProjection_transition X (baseIdealSheaf A I f) P n)

end Compare

/-! ### The comparison as an isomorphism of systems -/

section SystemIso

variable (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{u}}
  (f : X ⟶ Spec (.of A)) [IsLocallyNoetherian X] [LocallyOfFiniteType f]
  (Q : CoherentModulesProperOver f) (S : AdicCoherentModuleSystem A I f)
  (β : ∀ n : ℕ, ((completionFunctor X (baseIdealSheaf A I f)).obj Q.obj).obj.obj (op n) ≅
    adicPushforwardObj A I f S n)

/-- **The isomorphism of systems on the thickenings attached to a degreewise comparison on
`X`.** -/
public def adicThickeningEssSurjSystemIso
    (hβ : ∀ n : ℕ, ((completionFunctor X (baseIdealSheaf A I f)).obj Q.obj).obj.map
          (homOfLE (Nat.le_succ n)).op ≫ (β n).hom =
        (β (n + 1)).hom ≫ adicPushforwardTransition A I f S n) :
    (adicThickeningCompletionFunctor A I f).obj Q ≅ S where
  hom :=
    { app := fun n => (adicThickeningEssSurjIso A I f Q.obj S β n).hom
      comm := fun n => adicThickeningEssSurjIso_comm A I f Q.obj S β hβ n }
  inv :=
    { app := fun n => (adicThickeningEssSurjIso A I f Q.obj S β n).inv
      comm := fun n => inv_comp_eq_comp_inv_of_comm
        ((Scheme.Modules.pullback (adicBaseChangeSucc A I f n)).mapIso
          (adicThickeningEssSurjIso A I f Q.obj S β (n + 1)))
        (adicThickeningEssSurjIso A I f Q.obj S β n)
        (adicThickeningEssSurjIso_comm A I f Q.obj S β hβ n) }
  hom_inv_id := AdicCoherentModuleSystem.Hom.ext (funext fun n =>
    (adicThickeningEssSurjIso A I f Q.obj S β n).hom_inv_id)
  inv_hom_id := AdicCoherentModuleSystem.Hom.ext (funext fun n =>
    (adicThickeningEssSurjIso A I f Q.obj S β n).inv_hom_id)

end SystemIso

/-! ### The degreewise comparison of an isomorphism in the first picture -/

section Degreewise

variable (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{u}}
  (f : X ⟶ Spec (.of A)) [IsLocallyNoetherian X] [LocallyOfFiniteType f]
  (P : CoherentModulesProperOver f) (S : AdicCoherentModuleSystem A I f)

/-- The underlying isomorphism of inverse systems of `𝒪_X`-modules. -/
public def adicPushforwardSystemNatIso
    (α : (completionFunctorProperOver A I f).obj P ≅ adicPushforwardSystem A I f S) :
    ((completionFunctor X (baseIdealSheaf A I f)).obj P.obj).obj ≅
      adicPushforwardSystemFunctor A I f S :=
  (ObjectProperty.ι (Stacks.Coherent.IsCoherentAdicSystem (baseIdealSheaf A I f))).mapIso
    ((ObjectProperty.ι
      (fun F : Stacks.Coherent.CoherentAdicSystems (baseIdealSheaf A I f) =>
        HasProperSupport f (F.obj.obj (op 0)))).mapIso α)

/-- The component at `n` of `AlgebraicGeometry.adicPushforwardSystemNatIso`. -/
public def adicPushforwardDegreewiseIso
    (α : (completionFunctorProperOver A I f).obj P ≅ adicPushforwardSystem A I f S) (n : ℕ) :
    ((completionFunctor X (baseIdealSheaf A I f)).obj P.obj).obj.obj (op n) ≅
      adicPushforwardObj A I f S n :=
  (adicPushforwardSystemNatIso A I f P S α).app (op n)

/-- The components `AlgebraicGeometry.adicPushforwardDegreewiseIso` are compatible with the
transitions of the two systems. -/
public theorem adicPushforwardDegreewiseIso_comm
    (α : (completionFunctorProperOver A I f).obj P ≅ adicPushforwardSystem A I f S) (n : ℕ) :
    ((completionFunctor X (baseIdealSheaf A I f)).obj P.obj).obj.map
          (homOfLE (Nat.le_succ n)).op ≫ (adicPushforwardDegreewiseIso A I f P S α n).hom =
      (adicPushforwardDegreewiseIso A I f P S α (n + 1)).hom ≫
        adicPushforwardTransition A I f S n :=
  ((adicPushforwardSystemNatIso A I f P S α).hom.naturality
      (homOfLE (Nat.le_succ n)).op).trans
    (congrArg (fun z => (adicPushforwardDegreewiseIso A I f P S α (n + 1)).hom ≫ z)
      (Functor.ofOpSequence_map_homOfLE_succ
        (fun m => adicPushforwardTransition A I f S m) n))

end Degreewise

/-! ### Essential surjectivity, and `h088F` -/

/-- **The completion functor is essentially surjective.** For `A` Noetherian and `I`-adically
complete and `f` separated, locally of finite type and quasi-compact, every system `(ℱₙ, φₙ)` of
coherent modules on the adic thickenings, with the support of its first term proper over
`Spec (A / I)`, is the system of restrictions of a coherent `𝒪_X`-module with support proper
over `A`. -/
public theorem essSurj_adicThickeningCompletionFunctor
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    (adicThickeningCompletionFunctor A I f).EssSurj := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have := isEquivalence_completionFunctorProperOver_holds A I f
  refine ⟨fun S => ?_⟩
  let e := (completionFunctorProperOver A I f).objObjPreimageIso (adicPushforwardSystem A I f S)
  exact ⟨_, ⟨adicThickeningEssSurjSystemIso A I f _ S
    (adicPushforwardDegreewiseIso A I f _ S e) (adicPushforwardDegreewiseIso_comm A I f _ S e)⟩⟩

/-- **The completion functor is an equivalence.** Let `A` be a Noetherian
ring complete with respect to an ideal `I`, put `S = Spec A`, `Sₙ = Spec (A / Iⁿ)`, let
`f : X ⟶ S` be separated and of finite type (locally of finite type and quasi-compact) and
`Xₙ = X ×_S Sₙ`. Then the completion functor
`AlgebraicGeometry.adicThickeningCompletionFunctor`, from the coherent `𝒪_X`-modules with support
proper over `A` to the systems `(ℱₙ, φₙ)` — `ℱₙ` coherent on `Xₙ`, `φₙ : iₙ^*ℱₙ₊₁ ≅ ℱₙ`, and
`Supp(ℱ₁)` proper over `S₁` — sending `ℱ` to its restrictions `ℱ|_{Xₙ}`, is an equivalence of
categories. -/
@[stacks 088F "the completion functor from the coherent O_X-modules with support proper over A \
to the systems (F n, phi n) of clauses (1), (2) and (3) is an equivalence of categories, for A \
Noetherian and I-adically complete and X -> Spec A separated and of finite type"]
public theorem isEquivalence_adicThickeningCompletionFunctor
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    (adicThickeningCompletionFunctor A I f).IsEquivalence :=
  isEquivalence_adicThickeningCompletionFunctor_of_essSurj A I f
    (essSurj_adicThickeningCompletionFunctor A I f)

end AlgebraicGeometry

end
