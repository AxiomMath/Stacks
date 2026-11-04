module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.AdicThickeningEssSurj

/-!
# Stacks 088F over a proper base: the support conditions omitted

[Stacks, Tag 088F] ends: "In the special case that `X` is proper over `A` we can omit the
conditions on the supports." This file states that special case on its own terms. Let `A` be a
Noetherian ring complete with respect to an ideal `I` and let `f : X ⟶ Spec A` be proper, with
adic thickenings `Xₙ = X ×_S Sₙ` and transitions `iₙ : Xₙ ⟶ Xₙ₊₁`.

## Main definitions

* `AlgebraicGeometry.AdicCoherentTransitionSystem`: the systems `(ℱₙ, φₙ)` of clauses (1) and
  (2) of the remark alone: coherent `𝒪_{Xₙ}`-modules with isomorphisms `φₙ : iₙ^*ℱₙ₊₁ ≅ ℱₙ`,
  with no condition on the support of `ℱ₁`.
* `AlgebraicGeometry.adicThickeningTransitionCompletionFunctor`: completion `ℱ ↦ (ℱ|_{Xₙ})`
  from all coherent `𝒪_X`-modules into those systems.

## Main results

* `AlgebraicGeometry.isEquivalence_adicThickeningTransitionCompletionFunctor`: that functor is
  an equivalence of categories, for a proper `f`.

## Implementation notes

The proof compares with the support-restricted equivalence
`AlgebraicGeometry.isEquivalence_adicThickeningCompletionFunctor`: over a proper base the
inclusion of the coherent modules with proper support into all coherent modules is an
equivalence (`Stacks.Algebraization.hasProperSupport_of_isProper`), and forgetting the support
clause (3) of a system is an equivalence
(`AlgebraicGeometry.hasProperSupport_of_isProper_adicBaseChange`).

## References

* [Stacks Project, Tag 088F](https://stacks.math.columbia.edu/tag/088F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

open Stacks.Algebraization (HasProperSupport hasProperSupport_of_isProper
  CoherentModulesProperOver)

/-- The systems `(ℱₙ, φₙ)` of clauses (1) and (2) of [Stacks, Tag 088F]. For `f : X ⟶ Spec A`
locally of finite type, a coherent `𝒪_{Xₙ}`-module `ℱₙ` on every adic thickening together with an
isomorphism `φₙ : iₙ^* ℱₙ₊₁ ≅ ℱₙ` along every transition `iₙ : Xₙ ⟶ Xₙ₊₁`; no condition is put
on the support of `ℱ₁`. -/
public structure AdicCoherentTransitionSystem (A : Type u) [CommRing A] (I : Ideal A)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f] where
  /-- The sheaf of modules on the `n`-th adic thickening `Xₙ`. -/
  obj (n : ℕ) : (adicBaseChange A I f n).Modules
  /-- Clause (1): every term is coherent. -/
  isCoherent (n : ℕ) : _root_.SheafOfModules.IsCoherent.{u} (obj n)
  /-- Clause (2): the transition isomorphism `φₙ : iₙ^* ℱₙ₊₁ ≅ ℱₙ`. -/
  transitionIso (n : ℕ) :
    (Scheme.Modules.pullback (adicBaseChangeSucc A I f n)).obj (obj (n + 1)) ≅ obj n

namespace AdicCoherentTransitionSystem

variable {A : Type u} [CommRing A] {I : Ideal A} {X : Scheme.{u}} {f : X ⟶ Spec (.of A)}
  [LocallyOfFiniteType f]

/-- A morphism of systems: a map of sheaves of modules on every thickening, compatible with the
transition isomorphisms. -/
@[ext]
public structure Hom (F G : AdicCoherentTransitionSystem A I f) where
  /-- The component on the `n`-th thickening. -/
  app (n : ℕ) : F.obj n ⟶ G.obj n
  /-- Compatibility with the transition isomorphisms. -/
  comm (n : ℕ) :
    (Scheme.Modules.pullback (adicBaseChangeSucc A I f n)).map (app (n + 1)) ≫
        (G.transitionIso n).hom =
      (F.transitionIso n).hom ≫ app n

/-- The systems of clauses (1) and (2) form a category: morphisms are the compatible families of
maps `AdicCoherentTransitionSystem.Hom`, with componentwise identities and composition. -/
public instance : Category (AdicCoherentTransitionSystem A I f) where
  Hom F G := Hom F G
  id F :=
    { app := fun _ => 𝟙 _
      comm := fun n => by simp }
  comp {F G H} α β :=
    { app := fun n => α.app n ≫ β.app n
      comm := fun n => by
        rw [Functor.map_comp, Category.assoc, β.comm n, ← Category.assoc, α.comm n,
          Category.assoc] }
  id_comp _ := Hom.ext (funext fun _ => Category.id_comp _)
  comp_id _ := Hom.ext (funext fun _ => Category.comp_id _)
  assoc _ _ _ := Hom.ext (funext fun _ => Category.assoc _ _ _)

end AdicCoherentTransitionSystem

variable (A : Type u) [CommRing A] (I : Ideal A) {X : Scheme.{u}} (f : X ⟶ Spec (.of A))

/-- Forgetting clause (3): a system of Stacks 088F is in particular a system of clauses (1) and
(2). -/
public def AdicCoherentModuleSystem.forgetSupport [LocallyOfFiniteType f] :
    AdicCoherentModuleSystem A I f ⥤ AdicCoherentTransitionSystem A I f where
  obj F := ⟨F.obj, F.isCoherent, F.transitionIso⟩
  map φ := ⟨φ.app, φ.comm⟩

/-- Forgetting clause (3) is faithful: a morphism of systems is determined by its components. -/
public instance [LocallyOfFiniteType f] : (AdicCoherentModuleSystem.forgetSupport A I f).Faithful :=
  ⟨fun {_ _} _ _ h =>
    AdicCoherentModuleSystem.Hom.ext (congrArg AdicCoherentTransitionSystem.Hom.app h)⟩

/-- Forgetting clause (3) is full: a compatible family of maps between the underlying systems of
clauses (1) and (2) is already a morphism of systems of Stacks 088F. -/
public instance [LocallyOfFiniteType f] : (AdicCoherentModuleSystem.forgetSupport A I f).Full :=
  ⟨fun {_ _} φ => ⟨⟨φ.app, φ.comm⟩, rfl⟩⟩

/-- Over a proper base every system of clauses (1) and (2) satisfies clause (3), by
`AlgebraicGeometry.hasProperSupport_of_isProper_adicBaseChange`. -/
public instance [IsProper f] : (AdicCoherentModuleSystem.forgetSupport A I f).EssSurj :=
  ⟨fun G => ⟨AdicCoherentModuleSystem.ofIsProper A I f G.obj G.isCoherent G.transitionIso,
    ⟨Iso.refl _⟩⟩⟩

/-- Over a proper base, forgetting clause (3) is an equivalence. -/
public instance [IsProper f] : (AdicCoherentModuleSystem.forgetSupport A I f).IsEquivalence :=
  { }

/-- Over a proper base every coherent `𝒪_X`-module has support proper over the base: the whole
category of coherent modules, as the full subcategory of those with proper support. -/
public def coherentModulesToProperOver {S : Scheme.{u}} (g : X ⟶ S) [IsProper g] :
    AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf ⥤
      CoherentModulesProperOver g :=
  ObjectProperty.lift _ (𝟭 _) fun F =>
    have hcoh : F.obj.IsCoherent := F.property
    have : F.obj.IsFiniteType := hcoh.isFiniteType
    hasProperSupport_of_isProper g F.obj

/-- Viewing every coherent `𝒪_X`-module as one with proper support is faithful. -/
public instance {S : Scheme.{u}} (g : X ⟶ S) [IsProper g] :
    (coherentModulesToProperOver g).Faithful := by
  unfold coherentModulesToProperOver
  infer_instance

/-- Viewing every coherent `𝒪_X`-module as one with proper support is full. -/
public instance {S : Scheme.{u}} (g : X ⟶ S) [IsProper g] :
    (coherentModulesToProperOver g).Full := by
  unfold coherentModulesToProperOver
  infer_instance

/-- Over a proper base every coherent module with proper support is, up to the identity
isomorphism, a coherent `𝒪_X`-module viewed as one with proper support. -/
public instance {S : Scheme.{u}} (g : X ⟶ S) [IsProper g] :
    (coherentModulesToProperOver g).EssSurj :=
  ⟨fun F => ⟨F.obj, ⟨Iso.refl _⟩⟩⟩

/-- Over a proper base, viewing every coherent `𝒪_X`-module as one with proper support is an
equivalence. -/
public instance {S : Scheme.{u}} (g : X ⟶ S) [IsProper g] :
    (coherentModulesToProperOver g).IsEquivalence :=
  { }

/-- The completion functor of [Stacks, Tag 088F] on all coherent modules, for a proper `f`. A
coherent `𝒪_X`-module `ℱ` goes to the system `(ℱ|_{Xₙ})` of its restrictions to the adic
thickenings, with the transition isomorphisms `iₙ^*(ℱ|_{Xₙ₊₁}) ≅ ℱ|_{Xₙ}`; no support condition
is imposed on either side. On objects and morphisms it is
`AlgebraicGeometry.adicThickeningCompletionFunctor`, which is defined on the coherent modules with
proper support — all of them, over a proper base. -/
public def adicThickeningTransitionCompletionFunctor [IsNoetherianRing A] [IsProper f] :
    AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf ⥤
      AdicCoherentTransitionSystem A I f :=
  coherentModulesToProperOver f ⋙ adicThickeningCompletionFunctor A I f ⋙
    AdicCoherentModuleSystem.forgetSupport A I f

/-- The `n`-th term of the completion of `ℱ` is its restriction `ℱ|_{Xₙ}` to the `n`-th adic
thickening. -/
public theorem adicThickeningTransitionCompletionFunctor_obj_obj [IsNoetherianRing A]
    [IsProper f] (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) (n : ℕ) :
    ((adicThickeningTransitionCompletionFunctor A I f).obj F).obj n =
      adicThickeningCompletion A I f F.obj n :=
  rfl

/-- Let `A` be a Noetherian ring complete with respect to an ideal `I`, let `f : X ⟶ Spec A` be
proper and `Xₙ = X ×_S Sₙ`. Then completion `ℱ ↦ (ℱ|_{Xₙ})` is an equivalence from the category
of all coherent `𝒪_X`-modules to the category of systems `(ℱₙ, φₙ)` with `ℱₙ` a coherent
`𝒪_{Xₙ}`-module and `φₙ : iₙ^*ℱₙ₊₁ ≅ ℱₙ` an isomorphism. -/
@[stacks 088F "the special case of X proper over A, with the conditions on the supports \
omitted: completion from all coherent O_X-modules to the systems of coherent O_{X_n}-modules F n \
with isomorphisms phi n is an equivalence of categories"]
public theorem isEquivalence_adicThickeningTransitionCompletionFunctor [IsNoetherianRing A]
    [IsAdicComplete I A] [IsProper f] :
    (adicThickeningTransitionCompletionFunctor A I f).IsEquivalence := by
  have := isEquivalence_adicThickeningCompletionFunctor A I f
  unfold adicThickeningTransitionCompletionFunctor
  infer_instance

end AlgebraicGeometry

end
