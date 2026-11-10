module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProperGlobalSections.IdealKernelPower
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentCompletionProperSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentCompletionAlgebraization
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicDirectImageComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentHomColimitOverComplement
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperGlobalSections.FormalFunctionsFibres

/-!
# The statements of Grothendieck's existence theorem for algebraic spaces

This file states, as propositions, the steps of Grothendieck's existence and algebraization
theorems for algebraic spaces (Stacks, Sections 089N and 0A00), so that their proofs can be
developed independently of one another: a lemma using one of these steps takes the proposition
as a hypothesis until the step is proved, and the hypothesis is then discharged.  Nothing is
proved here beyond the local Noetherianity needed for the completion functor to be defined.

The setting is Situation 08B7 over an affine locally Noetherian object `V` of the big fppf site
over `S`: `A = Γ(V, 𝒪_V)`, an ideal `I ⊆ A`, and an algebraic space `X` with a morphism
`f : X ⟶ V`.  The sheaf of ideals `I 𝒪_X` is `AlgebraicGeometry.Space.idealKernel` of the
pullback of functions `A ⟶ Γ(X, 𝒪_X)`, and the infinitesimal neighbourhood
`X_n = X ×_V Spec (A / Iⁿ)` is `AlgebraicGeometry.Space.fibreSpace`.

## Main definitions

* `AlgebraicGeometry.Space.CompletionBijectiveOnHoms` — Stacks 08B9.
* `AlgebraicGeometry.Space.CompletionAlgebraizationExists` — Stacks 08BB, existence.
* `AlgebraicGeometry.Space.CompletionDirectImageComparisonExists` — Stacks 08BD.
* `AlgebraicGeometry.Space.CompletionEssImageOfAnnihilated` — Stacks 08BC.
* `AlgebraicGeometry.Space.CompletionProperOverIsEquivalence` — Stacks 08BE.
* `AlgebraicGeometry.Space.ClosedSubspaceTowerAlgebraizes` — Stacks 08BG.
* `AlgebraicGeometry.Space.ThickeningMapsAlgebraize` — Stacks 0A4Z.  Its form for a target
  separated and locally of finite type over `S`, with the thickenings spelled as pullbacks, is
  `AlgebraicGeometry.Space.HasProperTowerAlgebraization`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Situation

variable (V : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
  [_root_.AlgebraicGeometry.IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V)]
  (I : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] in
/-- An algebraic space locally of finite type over a locally Noetherian object of the site is
étale-locally Noetherian. -/
theorem hasEtaleLocalProperty_isLocallyNoetherian_of_isLocallyOfFiniteType_schemeSpace
    {X : AlgebraicSpaces B S hS} (f : X ⟶ schemeSpace V)
    (hf : IsLocallyOfFiniteType B S hS f.hom) :
    HasEtaleLocalProperty B S hS X.1
      (fun T : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian T) :=
  hasEtaleLocalProperty_isLocallyNoetherian_of_isLocallyOfFiniteType B S hS X.2
    (isAlgebraicSpace_yoneda B S hS V) f.hom hf
    (hasEtaleLocalProperty_isLocallyNoetherian_yoneda inferInstance)

/-- The completion functor `Coh(𝒪_X) ⥤ Coh(X, I 𝒪_X)` of Stacks 08B4 for an algebraic space
locally of finite type over `V`. -/
abbrev completionFunctorOver {X : AlgebraicSpaces B S hS} (f : X ⟶ schemeSpace V)
    (hf : IsLocallyOfFiniteType B S hS f.hom) :
    CoherentModules.{u, u} B S hS X.1 X.2 ⥤
      CoherentAdicSystems B S hS X.1 X.2 (idealKernel (pullbackRingHom B V f) I) :=
  haveI : Fact (HasEtaleLocalProperty B S hS X.1
      (fun T : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian T)) :=
    ⟨hasEtaleLocalProperty_isLocallyNoetherian_of_isLocallyOfFiniteType_schemeSpace V f hf⟩
  completionFunctor B S hS X.1 X.2 (idealKernel (pullbackRingHom B V f) I)
    (isQuasicoherentOnSite_idealKernel (pullbackRingHom B V f) I)

/-- The arrow of equation 76.42.5.1 (Stacks 08B8) for an algebraic space locally of finite type
over `V`. -/
abbrev completionFunctorProperOverBase {X : AlgebraicSpaces B S hS} (f : X ⟶ schemeSpace V)
    (hf : IsLocallyOfFiniteType B S hS f.hom) :
    CoherentModulesProperOver B S hS X.2 (schemeSpace V).2 f.hom hf ⥤
      CoherentAdicSystemsProperOver B S hS X.2 (schemeSpace V).2 f.hom hf
        (idealKernel (pullbackRingHom B V f) I) :=
  haveI : Fact (HasEtaleLocalProperty B S hS X.1
      (fun T : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian T)) :=
    ⟨hasEtaleLocalProperty_isLocallyNoetherian_of_isLocallyOfFiniteType_schemeSpace V f hf⟩
  completionFunctorProperOver B S hS X.1 (schemeSpace V).1 X.2 (schemeSpace V).2 f.hom hf
    (idealKernel (pullbackRingHom B V f) I)
    (isQuasicoherentOnSite_idealKernel (pullbackRingHom B V f) I)

/-- The support of a coherent module, as a set of points. -/
abbrev coherentSupport {X : AlgebraicSpaces B S hS} (M : CoherentModules.{u, u} B S hS X.1 X.2) :
    Set (points B S hS X.1) :=
  supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj M.obj)

/-- **Stacks 08B9.** In Situation 08B7, for coherent `𝒪_X`-modules `M`, `N` whose supports meet
in a closed subset proper over `V`, completion is a bijection
`Hom(M, N) ≃ Hom_{Coh(X, I 𝒪_X)}(M^∧, N^∧)`. -/
def CompletionBijectiveOnHoms {X : AlgebraicSpaces B S hS} (f : X ⟶ schemeSpace V) : Prop :=
  IsAdicComplete I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) →
    IsSeparated B S hS f.hom → ∀ hft : IsFiniteType B S hS f.hom,
    ∀ (M N : CoherentModules.{u, u} B S hS X.1 X.2)
      (hT : IsClosed (coherentSupport M ∩ coherentSupport N)),
      IsProperOver B S hS X.2 (schemeSpace V).2 f.hom hft.1
        (coherentSupport M ∩ coherentSupport N) hT →
      Function.Bijective (fun a : M ⟶ N => (completionFunctorOver V I f hft.1).map a)

/-- **Stacks 08BE (Grothendieck's existence theorem).** In Situation 08B7 the completion functor
`Coh_{support proper over A}(𝒪_X) ⥤ Coh_{support proper over A}(X, I 𝒪_X)` is an equivalence. -/
def CompletionProperOverIsEquivalence {X : AlgebraicSpaces B S hS} (f : X ⟶ schemeSpace V) :
    Prop :=
  IsAdicComplete I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) →
    IsSeparated B S hS f.hom → ∀ hft : IsFiniteType B S hS f.hom,
    (completionFunctorProperOverBase V I f hft.1).IsEquivalence

/-- **Stacks 08BC**, with `Coh(𝒪_{X_e})` read as the coherent `𝒪_X`-modules annihilated by
`𝓚ᵉ` (Stacks 08AM) and its hypothesis (1) read, given the full faithfulness of Stacks 08B9, as
essential surjectivity onto the objects annihilated by `𝓚ᵉ`.  In Situation 08B7, let `𝓚 ⊆ 𝒪_X`
be a quasi-coherent sheaf of ideals and `E` an object of
`Coh_{support proper over A}(X, I 𝒪_X)`.  If every object annihilated by a power `𝓚ᵉ`, `e ≥ 1`,
is in the essential image of the completion functor, and if there is a coherent `𝓗` with support
proper over `A` and a map `E ⟶ 𝓗^∧` whose levelwise kernels and cokernels are annihilated by a
power of `𝓚`, then `E` is in the essential image. -/
def CompletionEssImageOfAnnihilated {X : AlgebraicSpaces B S hS} (f : X ⟶ schemeSpace V) :
    Prop :=
  IsAdicComplete I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) →
    IsSeparated B S hS f.hom → ∀ hft : IsFiniteType B S hS f.hom,
    ∀ (𝓚 : (SheafOfModules.unit
        ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS X.1 X.2).O))).Submodule),
      𝓚.toSheafOfModules.IsQuasicoherentOnSite →
    ∀ E : CoherentAdicSystemsProperOver B S hS X.2 (schemeSpace V).2 f.hom hft.1
        (idealKernel (pullbackRingHom B V f) I),
      (∀ e : ℕ, 0 < e →
        ∀ E' : CoherentAdicSystemsProperOver B S hS X.2 (schemeSpace V).2 f.hom hft.1
          (idealKernel (pullbackRingHom B V f) I),
          (∀ n : ℕ, idealPowerMultiple B S hS X.1 X.2 𝓚 e (E'.obj.obj.obj (op n)) = ⊥) →
          (completionFunctorProperOverBase V I f hft.1).essImage E') →
      (∃ (H : CoherentModulesProperOver B S hS X.2 (schemeSpace V).2 f.hom hft.1)
        (α : E ⟶ (completionFunctorProperOverBase V I f hft.1).obj H),
        ∃ t : ℕ, 0 < t ∧ ∀ k : ℕ,
          idealPowerMultiple B S hS X.1 X.2 𝓚 t (kernel (α.hom.hom.app (op k))) = ⊥ ∧
            idealPowerMultiple B S hS X.1 X.2 𝓚 t (cokernel (α.hom.hom.app (op k))) = ⊥) →
      (completionFunctorProperOverBase V I f hft.1).essImage E

/-- The closed subspace `X_n = X ×_V Spec (A / Iⁿ)` of `X`. -/
abbrev thickeningSubspace {X : AlgebraicSpaces B S hS} (f : X ⟶ schemeSpace V) (n : ℕ) :
    ClosedSubspaces B S hS X.1 :=
  fibreThickening V I f n

/-- **Stacks 08BG**, for a compatible system of closed subspaces `Z_n ⊆ X_n`.  In Situation 08B7
let `Z_n ⊆ X` be closed subspaces with `Z_n ⊆ X_n` and `Z_n = Z_{n+1} ∩ X_n` for `n ≥ 1`, with
`Z_1` proper over `V`.  Then there is a closed subspace `Z ⊆ X` proper over `V` with
`Z ∩ X_n = Z_n` for all `n ≥ 1`. -/
def ClosedSubspaceTowerAlgebraizes {X : AlgebraicSpaces B S hS} (f : X ⟶ schemeSpace V) : Prop :=
  IsAdicComplete I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) →
    IsSeparated B S hS f.hom → IsFiniteType B S hS f.hom →
    ∀ Z : ℕ → ClosedSubspaces B S hS X.1,
      (∀ n, 1 ≤ n → (Z n).1 ≤ (thickeningSubspace V I f n).1) →
      (∀ n, 1 ≤ n → (Z n).1 = (Z (n + 1)).1 ⊓ (thickeningSubspace V I f n).1) →
      IsProper B S hS (subspaceInclusion B S hS X (Z 1) ≫ f).hom →
      ∃ Z' : ClosedSubspaces B S hS X.1,
        IsProper B S hS (subspaceInclusion B S hS X Z' ≫ f).hom ∧
          ∀ n, 1 ≤ n → Z'.1 ⊓ (thickeningSubspace V I f n).1 = (Z n).1

/-- **Stacks 0A4Z.** Let `A` be Noetherian and `I`-adically complete, `X` proper over `V` and `Y`
separated of finite type over `V`.  A system of morphisms `g_n : X_n ⟶ Y` over `V`, compatible
with the inclusions `X_m ⊆ X_n`, comes from a unique morphism `g : X ⟶ Y` over `V`.  (A morphism
`X_n ⟶ Y` over `V` is a morphism `X_n ⟶ Y_n = Y ×_V Spec (A / Iⁿ)` over `Spec (A / Iⁿ)`.) -/
def ThickeningMapsAlgebraize : Prop :=
  IsAdicComplete I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) →
    ∀ (X Y : AlgebraicSpaces B S hS) (p : X ⟶ schemeSpace V) (q : Y ⟶ schemeSpace V),
      IsProper B S hS p.hom → IsSeparated B S hS q.hom → IsFiniteType B S hS q.hom →
    ∀ g : ∀ n : ℕ, fibreSpace V I p n ⟶ Y,
      (∀ n, g n ≫ q = fibreInclusion V I p n ≫ p) →
      (∀ (m n : ℕ) (h : m ≤ n), fibreTransition V I p h ≫ g n = g m) →
      ∃! g' : X ⟶ Y, g' ≫ q = p ∧ ∀ n, fibreInclusion V I p n ≫ g' = g n

end Situation

section Noetherian

variable (hZ : B.Contains (⊤_ Scheme.{u}))

/-- **Stacks 08BB, existence.** Let `X` be a Noetherian algebraic space, `𝓘 ⊆ 𝒪_X` a
quasi-coherent sheaf of ideals, `G` a coherent `𝒪_X`-module, `E` an object of `Coh(X, 𝓘)` and
`α : E ⟶ G^∧` a map whose levelwise kernels and cokernels are annihilated by a power of `𝓘`.
Then there are a coherent `M`, a map `a : M ⟶ G` whose kernel and cokernel are annihilated by a
power of `𝓘`, and an isomorphism `β : E ≅ M^∧` with `α = β ≫ a^∧`.  (Uniqueness is
`AlgebraicGeometry.Space.existsUnique_iso_of_algebraization_of_isNoetherian`.) -/
def CompletionAlgebraizationExists (X : AlgebraicSpaces B S hS) : Prop :=
  IsNoetherian B S hS hZ X.1 →
    ∀ (𝓘 : (SheafOfModules.unit
        ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS X.1 X.2).O))).Submodule)
      (hI : 𝓘.toSheafOfModules.IsQuasicoherentOnSite)
      [Fact (HasEtaleLocalProperty B S hS X.1
        (fun T : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian T))]
      (G : CoherentModules.{u, u} B S hS X.1 X.2) (E : CoherentAdicSystems B S hS X.1 X.2 𝓘)
      (α : E ⟶ (completionFunctor B S hS X.1 X.2 𝓘 hI).obj G),
      (∃ t : ℕ, 0 < t ∧ ∀ k : ℕ,
        idealPowerMultiple B S hS X.1 X.2 𝓘 t (kernel (α.hom.app (op k))) = ⊥ ∧
          idealPowerMultiple B S hS X.1 X.2 𝓘 t (cokernel (α.hom.app (op k))) = ⊥) →
      ∃ (M : CoherentModules.{u, u} B S hS X.1 X.2) (a : M ⟶ G)
        (β : E ≅ (completionFunctor B S hS X.1 X.2 𝓘 hI).obj M),
        IsMapKernelCokernelAnnihilatedByPower B S hS X.1 X.2 𝓘 a ∧
          α = β.hom ≫ (completionFunctor B S hS X.1 X.2 𝓘 hI).map a

/-- **Stacks 08BD.** Let `f : X ⟶ Y` be a representable proper morphism of Noetherian algebraic
spaces, `𝓙, 𝓚 ⊆ 𝒪_Y` quasi-coherent sheaves of ideals with `f` an isomorphism over
`Y ∖ V(𝓚)`, and `𝓘 = f⁻¹𝓙 𝒪_X` (in the form `AlgebraicGeometry.Space.IdealPowerMultipleCompatible`
of the pullback).  For `(𝓖_n)` in `Coh(Y, 𝓙)`, `𝓕` coherent on `X` and an isomorphism
`β : (f^*𝓖_n) ≅ 𝓕^∧`, the direct image `f_*𝓕` is coherent and there is a map
`α : (𝓖_n) ⟶ (f_*𝓕)^∧` in `Coh(Y, 𝓙)` whose levelwise kernels and cokernels are annihilated by
a power of `𝓚`. -/
def CompletionDirectImageComparisonExists {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) : Prop :=
  IsNoetherian B S hS hZ X.1 → IsNoetherian B S hS hZ Y.1 →
    yoneda.relativelyRepresentable f.hom → IsProper B S hS f.hom →
    ∀ (𝓙 𝓚 : (SheafOfModules.unit
        ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS Y.1 Y.2).O))).Submodule)
      (hJ : 𝓙.toSheafOfModules.IsQuasicoherentOnSite)
      (_hK : 𝓚.toSheafOfModules.IsQuasicoherentOnSite),
      IsIso (pullback.snd f.hom (idealComplementι B S hS Y 𝓚).hom) →
    ∀ (𝓘 : (SheafOfModules.unit
        ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS X.1 X.2).O))).Submodule)
      (hI : 𝓘.toSheafOfModules.IsQuasicoherentOnSite),
      IdealPowerMultipleCompatible B S hS (modulePullback B S hS f) 𝓙 𝓘 →
    ∀ [Fact (HasEtaleLocalProperty B S hS X.1
        (fun T : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian T))]
      [Fact (HasEtaleLocalProperty B S hS Y.1
        (fun T : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian T))]
      (G : CoherentAdicSystems B S hS Y.1 Y.2 𝓙) (F : CoherentModules.{u, u} B S hS X.1 X.2),
      (G.obj ⋙ modulePullback B S hS f ≅ ((completionFunctor B S hS X.1 X.2 𝓘 hI).obj F).obj) →
      ∃ (hc : IsCoherent B S hS Y.1 Y.2 ((modulePushforward B S hS f).obj F.obj))
        (α : G ⟶ (completionFunctor B S hS Y.1 Y.2 𝓙 hJ).obj
          ⟨(modulePushforward B S hS f).obj F.obj, hc⟩),
        ∃ t : ℕ, 0 < t ∧ ∀ k : ℕ,
          idealPowerMultiple B S hS Y.1 Y.2 𝓚 t (kernel (α.hom.app (op k))) = ⊥ ∧
            idealPowerMultiple B S hS Y.1 Y.2 𝓚 t (cokernel (α.hom.app (op k))) = ⊥

end Noetherian

end AlgebraicGeometry.Space

end
