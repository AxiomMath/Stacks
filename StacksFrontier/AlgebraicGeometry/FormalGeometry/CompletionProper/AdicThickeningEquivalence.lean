module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.AdicThickeningTransitionDescent
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.AdicUnitConditionDescent

/-!
# The completion functor on adic thickenings is fully faithful

Let `A` be Noetherian and `I`-adically complete, and let `f : X ⟶ Spec A` be separated, locally
of finite type and quasi-compact. The functor
`AlgebraicGeometry.adicThickeningCompletionFunctor A I f` sends a coherent `𝒪_X`-module with
support proper over `A` to the system `(ℱ|_{Xₙ})` of its restrictions to the adic thickenings.
This file proves that this functor is fully faithful, and hence an equivalence of categories as
soon as it is essentially surjective.

## Main results

* `AlgebraicGeometry.comp_map_eq_map_comp_of_unit_comp`: for a factorisation `c ≫ h = k`,
  morphisms `m₁` over `h` and `m₀` over `k` that are compatible through the comparisons of the
  factorisation are compatible with the pushed-forward transitions.
* `AlgebraicGeometry.adicThickeningPushforwardTransition_comp_map`: a family of morphisms on the
  thickenings compatible with the transitions is compatible with the pushed-forward transitions.
* `AlgebraicGeometry.adicThickeningCompletionHomEquiv_symm_naturality`: such a family is carried
  by `AlgebraicGeometry.adicThickeningCompletionHomEquiv`, read backwards, to a family compatible
  with the quotient transitions of `Stacks.Algebraization.completionFunctor`.
* `AlgebraicGeometry.faithful_adicThickeningCompletionFunctor`,
  `AlgebraicGeometry.full_adicThickeningCompletionFunctor`: the completion functor is faithful
  and full.
* `AlgebraicGeometry.isEquivalence_adicThickeningCompletionFunctor_of_essSurj`: the completion
  functor is an equivalence if it is essentially surjective.
* `AlgebraicGeometry.isEquivalence_adicThickeningCompletionFunctor_of_comparisonFunctor`: the
  completion functor is an equivalence given an equivalence `Φ` of the target categories with
  `completionFunctorProperOver A I f ⋙ Φ ≅ adicThickeningCompletionFunctor A I f`.

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

/-! ### A family of morphisms on the thickenings against the pushed-forward transitions -/

section Generic

variable {Z Z' Z'' : Scheme.{u}}

/-- **A family of morphisms compatible downstairs is compatible with the pushed-forward
transitions.** Let `c ≫ h = k` be a factorisation, let `F` and `G` be modules on the base, and
suppose given

* morphisms `TF : h_*(h^* F) ⟶ k_*(k^* F)` and `TG : h_*(h^* G) ⟶ k_*(k^* G)` — the pushed-forward
  transitions — each carrying the unit of `h^* ⊣ h_*` to the unit of `k^* ⊣ k_*`, the units at `h`
  being epimorphisms;
* comparisons `ΘF` and `ΘG` equal to `Stacks.Descent.pullbackCompHom` of the factorisation;
* morphisms `m₁ : h^* F ⟶ h^* G` and `m₀ : k^* F ⟶ k^* G` such that `m₁` pulled back along `c`
  and read through the two comparisons is `m₀`.

Then `TF ≫ k_* m₀ = h_* m₁ ≫ TG`. -/
public theorem comp_map_eq_map_comp_of_unit_comp (h : Z' ⟶ Z) (c : Z'' ⟶ Z')
    {k : Z'' ⟶ Z} (hk : c ≫ h = k) (F G : Z.Modules)
    (hepiF : Epi ((Scheme.Modules.pullbackPushforwardAdjunction h).unit.app F))
    (hepiG : Epi ((Scheme.Modules.pullbackPushforwardAdjunction h).unit.app G))
    {TF : (Scheme.Modules.pushforward h).obj ((Scheme.Modules.pullback h).obj F) ⟶
      (Scheme.Modules.pushforward k).obj ((Scheme.Modules.pullback k).obj F)}
    {TG : (Scheme.Modules.pushforward h).obj ((Scheme.Modules.pullback h).obj G) ⟶
      (Scheme.Modules.pushforward k).obj ((Scheme.Modules.pullback k).obj G)}
    (hTF : (Scheme.Modules.pullbackPushforwardAdjunction h).unit.app F ≫ TF =
      (Scheme.Modules.pullbackPushforwardAdjunction k).unit.app F)
    (hTG : (Scheme.Modules.pullbackPushforwardAdjunction h).unit.app G ≫ TG =
      (Scheme.Modules.pullbackPushforwardAdjunction k).unit.app G)
    {m₁ : (Scheme.Modules.pullback h).obj F ⟶ (Scheme.Modules.pullback h).obj G}
    {m₀ : (Scheme.Modules.pullback k).obj F ⟶ (Scheme.Modules.pullback k).obj G}
    {ΘF : (Scheme.Modules.pullback c).obj ((Scheme.Modules.pullback h).obj F) ⟶
      (Scheme.Modules.pullback k).obj F}
    {ΘG : (Scheme.Modules.pullback c).obj ((Scheme.Modules.pullback h).obj G) ⟶
      (Scheme.Modules.pullback k).obj G}
    (hΘF : ΘF = pullbackCompHom c h k hk F)
    (hΘG : ΘG = pullbackCompHom c h k hk G)
    (hm : (Scheme.Modules.pullback c).map m₁ ≫ ΘG = ΘF ≫ m₀) :
    TF ≫ (Scheme.Modules.pushforward k).map m₀ =
      (Scheme.Modules.pushforward h).map m₁ ≫ TG := by
  have hTG' : TG = (pushUnit h c k hk).app ((Scheme.Modules.pullback h).obj G) ≫
      (Scheme.Modules.pushforward k).map ΘG := by
    refine (@cancel_epi _ _ _ _ _ _ hepiG _ _).mp ?_
    rw [hTG, hΘG, unit_comp_pushUnit_comp_map_pullbackCompHom h c hk G]
  refine (@cancel_epi _ _ _ _ _ _ hepiF _ _).mp ?_
  rw [← Category.assoc, hTF, hTG',
    ← Category.assoc ((Scheme.Modules.pushforward h).map m₁),
    (pushUnit h c k hk).naturality m₁]
  simp only [Functor.comp_map, Category.assoc, ← Functor.map_comp]
  rw [hm, Functor.map_comp, hΘF,
    ← Category.assoc ((pushUnit h c k hk).app ((Scheme.Modules.pullback h).obj F))
      ((Scheme.Modules.pushforward k).map (pullbackCompHom c h k hk F))
      ((Scheme.Modules.pushforward k).map m₀),
    ← Category.assoc, unit_comp_pushUnit_comp_map_pullbackCompHom h c hk F]

/-- **A square conjugated by two pairs of isomorphisms still commutes.** If
`TP = e₁.inv ≫ tP ≫ e₀.hom`, `TQ = d₁.inv ≫ tQ ≫ d₀.hom` and `TP ≫ p₀ = p₁ ≫ TQ`, then
`tP ≫ e₀.hom ≫ p₀ ≫ d₀.inv = (e₁.hom ≫ p₁ ≫ d₁.inv) ≫ tQ`. -/
private theorem comp_comp_eq_of_conjugated_square {C : Type*} [Category C]
    {P₁ P₀ Q₁ Q₀ R₁ R₀ S₁ S₀ : C} (e₁ : P₁ ≅ Q₁) (e₀ : P₀ ≅ Q₀) (d₁ : R₁ ≅ S₁) (d₀ : R₀ ≅ S₀)
    {tP : P₁ ⟶ P₀} {tQ : R₁ ⟶ R₀} {p₀ : Q₀ ⟶ S₀} {p₁ : Q₁ ⟶ S₁} {TP : Q₁ ⟶ Q₀} {TQ : S₁ ⟶ S₀}
    (hTP : TP = e₁.inv ≫ tP ≫ e₀.hom) (hTQ : TQ = d₁.inv ≫ tQ ≫ d₀.hom)
    (hsq : TP ≫ p₀ = p₁ ≫ TQ) :
    tP ≫ e₀.hom ≫ p₀ ≫ d₀.inv = (e₁.hom ≫ p₁ ≫ d₁.inv) ≫ tQ := by
  have h₁ : e₁.hom ≫ TP ≫ p₀ ≫ d₀.inv = tP ≫ e₀.hom ≫ p₀ ≫ d₀.inv := by
    rw [hTP]; simp
  have h₂ : e₁.hom ≫ p₁ ≫ TQ ≫ d₀.inv = (e₁.hom ≫ p₁ ≫ d₁.inv) ≫ tQ := by
    rw [hTQ]; simp
  refine h₁.symm.trans (Eq.trans (congrArg (fun z => e₁.hom ≫ z) ?_) h₂)
  rw [← Category.assoc, hsq, Category.assoc]

end Generic

/-! ### The transitions of the first picture against a family on the thickenings -/

section Adic

variable (A : Type u) [CommRing A] (I : Ideal A) {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
  [IsLocallyNoetherian X] [LocallyOfFiniteType f]
  (P Q : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)

omit [LocallyOfFiniteType f] in
/-- The inverse of `AlgebraicGeometry.adicThickeningCompletionHomEquiv` written out: the direct
image of the morphism on the thickening, conjugated by the unwinding at both ends. -/
public theorem adicThickeningCompletionHomEquiv_symm_apply (n : ℕ)
    (w : adicThickeningCompletion A I f P.obj n ⟶ adicThickeningCompletion A I f Q.obj n) :
    (adicThickeningCompletionHomEquiv A I f n P Q).symm w =
      (adicThickeningCompletionPushforwardIso A I f P n).hom ≫
        (Scheme.Modules.pushforward (pullback.fst f (adicThickeningι A I n))).map w ≫
          (adicThickeningCompletionPushforwardIso A I f Q n).inv :=
  rfl

/-- **A family of morphisms on the thickenings compatible with the canonical transitions is
compatible with the pushed-forward transitions.** The hypothesis is the compatibility condition
of `AlgebraicGeometry.AdicCoherentModuleSystem.Hom`, read at the two completions. -/
public theorem adicThickeningPushforwardTransition_comp_map
    (m : ∀ n : ℕ,
      adicThickeningCompletion A I f P.obj n ⟶ adicThickeningCompletion A I f Q.obj n)
    (hm : ∀ n : ℕ, (Scheme.Modules.pullback (adicBaseChangeSucc A I f n)).map (m (n + 1)) ≫
        (adicThickeningCompletionTransition A I f Q.obj n).hom =
      (adicThickeningCompletionTransition A I f P.obj n).hom ≫ m n)
    (n : ℕ) :
    adicThickeningPushforwardTransition A I f P n ≫
        (Scheme.Modules.pushforward (pullback.fst f (adicThickeningι A I n))).map (m n) =
      (Scheme.Modules.pushforward
            (pullback.fst f (adicThickeningι A I (n + 1)))).map (m (n + 1)) ≫
        adicThickeningPushforwardTransition A I f Q n :=
  have key (R : X.Modules) : (adicThickeningCompletionTransition A I f R n).hom =
      pullbackCompHom (adicBaseChangeSucc A I f n)
        (pullback.fst f (adicThickeningι A I (n + 1)))
        (pullback.fst f (adicThickeningι A I n)) (adicBaseChangeSucc_fst A I f n) R :=
    (pullbackComp_pullbackCongr_app_eq_adicThickeningCompletionTransition A I f n R).symm
  comp_map_eq_map_comp_of_unit_comp (pullback.fst f (adicThickeningι A I (n + 1)))
    (adicBaseChangeSucc A I f n) (adicBaseChangeSucc_fst A I f n) P.obj Q.obj
    (epi_unit_app_adicThickeningCompletion A I f P (n + 1))
    (epi_unit_app_adicThickeningCompletion A I f Q (n + 1))
    (unit_comp_adicThickeningPushforwardTransition A I f P n)
    (unit_comp_adicThickeningPushforwardTransition A I f Q n)
    (key P.obj) (key Q.obj)
    (hm n)

/-- **The naturality of the family read backwards through the degreewise identification.** A
family of morphisms on the thickenings compatible with the canonical transitions is carried by
`AlgebraicGeometry.adicThickeningCompletionHomEquiv`, read backwards, to a family compatible with
the quotient transitions of `Stacks.Algebraization.completionFunctor` — that is, to a natural
transformation of the inverse systems. -/
public theorem adicThickeningCompletionHomEquiv_symm_naturality
    (m : ∀ n : ℕ,
      adicThickeningCompletion A I f P.obj n ⟶ adicThickeningCompletion A I f Q.obj n)
    (hm : ∀ n : ℕ, (Scheme.Modules.pullback (adicBaseChangeSucc A I f n)).map (m (n + 1)) ≫
        (adicThickeningCompletionTransition A I f Q.obj n).hom =
      (adicThickeningCompletionTransition A I f P.obj n).hom ≫ m n)
    (n : ℕ) :
    ((completionFunctor X (baseIdealSheaf A I f)).obj P).obj.map
          (homOfLE (Nat.le_succ n)).op ≫
        (adicThickeningCompletionHomEquiv A I f n P Q).symm (m n) =
      (adicThickeningCompletionHomEquiv A I f (n + 1) P Q).symm (m (n + 1)) ≫
        ((completionFunctor X (baseIdealSheaf A I f)).obj Q).obj.map
          (homOfLE (Nat.le_succ n)).op := by
  refine Eq.trans (congrArg (fun z =>
      ((completionFunctor X (baseIdealSheaf A I f)).obj P).obj.map
          (homOfLE (Nat.le_succ n)).op ≫ z)
    (adicThickeningCompletionHomEquiv_symm_apply A I f P Q n (m n))) ?_
  refine Eq.trans ?_ (congrArg (fun z => z ≫
      ((completionFunctor X (baseIdealSheaf A I f)).obj Q).obj.map
        (homOfLE (Nat.le_succ n)).op)
    (adicThickeningCompletionHomEquiv_symm_apply A I f P Q (n + 1) (m (n + 1))).symm)
  exact comp_comp_eq_of_conjugated_square
    (adicThickeningCompletionPushforwardIso A I f P (n + 1))
    (adicThickeningCompletionPushforwardIso A I f P n)
    (adicThickeningCompletionPushforwardIso A I f Q (n + 1))
    (adicThickeningCompletionPushforwardIso A I f Q n) rfl rfl
    (adicThickeningPushforwardTransition_comp_map A I f P Q m hm n)

end Adic

/-- **The completion functor is faithful.** For `A` Noetherian and `I`-adically complete and `f`
separated, locally of finite type and quasi-compact, two maps of coherent `𝒪_X`-modules with
support proper over `A` that restrict to the same map on every adic thickening `Xₙ` are equal. -/
public theorem faithful_adicThickeningCompletionFunctor
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    (adicThickeningCompletionFunctor A I f).Faithful := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have := isEquivalence_completionFunctorProperOver_holds A I f
  refine ⟨fun {P Q} φ ψ h => ?_⟩
  refine Functor.map_injective (completionFunctorProperOver A I f) ?_
  refine ObjectProperty.hom_ext _ (ObjectProperty.hom_ext _ (NatTrans.ext (funext ?_)))
  intro m
  induction m using Opposite.rec with
  | op n =>
    refine (adicThickeningCompletionHomEquiv A I f n P.obj Q.obj).injective ?_
    refine (adicThickeningCompletionHomEquiv_completionFunctor_map A I f n φ.hom).trans ?_
    refine Eq.trans ?_ (adicThickeningCompletionHomEquiv_completionFunctor_map A I f n ψ.hom).symm
    exact congrArg (fun α : (adicThickeningCompletionFunctor A I f).obj P ⟶
      (adicThickeningCompletionFunctor A I f).obj Q =>
      AdicCoherentModuleSystem.Hom.app α n) h

/-- **The completion functor is full.** For `A` Noetherian and `I`-adically complete and `f`
separated, locally of finite type and quasi-compact, a compatible family of maps of the
restrictions to the adic thickenings comes from a map of coherent `𝒪_X`-modules with support
proper over `A`. -/
public theorem full_adicThickeningCompletionFunctor
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    (adicThickeningCompletionFunctor A I f).Full := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have := isEquivalence_completionFunctorProperOver_holds A I f
  refine ⟨fun {P Q} m => ?_⟩
  obtain ⟨φ, hφ⟩ := Functor.map_surjective (completionFunctorProperOver A I f)
    (ObjectProperty.homMk (ObjectProperty.homMk (NatTrans.ofOpSequence
      (fun n => (adicThickeningCompletionHomEquiv A I f n P.obj Q.obj).symm (m.app n))
      (adicThickeningCompletionHomEquiv_symm_naturality A I f P.obj Q.obj
        (fun n => m.app n) (fun n => m.comm n)))))
  refine ⟨φ, AdicCoherentModuleSystem.Hom.ext (funext fun n => ?_)⟩
  refine Eq.trans
    (adicThickeningCompletionHomEquiv_completionFunctor_map A I f n φ.hom).symm ?_
  refine Eq.trans (congrArg (adicThickeningCompletionHomEquiv A I f n P.obj Q.obj)
    (congrArg (fun z : (completionFunctorProperOver A I f).obj P ⟶
        (completionFunctorProperOver A I f).obj Q => z.hom.hom.app (op n)) hφ)) ?_
  exact Equiv.apply_symm_apply _ _

/-- **The completion functor is an equivalence if it is essentially surjective.** -/
public theorem isEquivalence_adicThickeningCompletionFunctor_of_essSurj
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (hessSurj : (adicThickeningCompletionFunctor A I f).EssSurj) :
    (adicThickeningCompletionFunctor A I f).IsEquivalence where
  faithful := faithful_adicThickeningCompletionFunctor A I f
  full := full_adicThickeningCompletionFunctor A I f
  essSurj := hessSurj

/-- **The completion functor is an equivalence given a comparison of the target categories.**
If `Φ : CoherentAdicSystemsProperOver f (baseIdealSheaf A I f) ⥤ AdicCoherentModuleSystem A I f`
is an equivalence and
`completionFunctorProperOver A I f ⋙ Φ ≅ adicThickeningCompletionFunctor A I f`, then
`AlgebraicGeometry.adicThickeningCompletionFunctor A I f` is an equivalence. -/
public theorem isEquivalence_adicThickeningCompletionFunctor_of_comparisonFunctor
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (Φ : CoherentAdicSystemsProperOver f (baseIdealSheaf A I f) ⥤
      AdicCoherentModuleSystem A I f)
    (hΦ : Φ.IsEquivalence)
    (e : completionFunctorProperOver A I f ⋙ Φ ≅ adicThickeningCompletionFunctor A I f) :
    (adicThickeningCompletionFunctor A I f).IsEquivalence :=
  have := hΦ
  have := isEquivalence_completionFunctorProperOver_holds A I f
  Functor.isEquivalence_of_iso e

end AlgebraicGeometry

end
