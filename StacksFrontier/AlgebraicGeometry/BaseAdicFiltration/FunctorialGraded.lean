module

public import StacksFrontier.AlgebraicGeometry.BaseAdicFiltration.Functorial
public import StacksFrontier.AlgebraicGeometry.BaseAdicFiltration.StructureSheaf

/-!
# The comparison of the filtration sequences, and the induction up the filtration

Let `g : U ⟶ V` be a morphism of schemes over `Spec A` (`g ≫ p_V = p_U`), let `I ⊆ A` be an
ideal, and let `φ : ℱ_V ⟶ g_* ℱ_U` be a morphism of `𝒪_V`-modules, with comparison maps
`c_n : ℱ_V/Iⁿℱ_V ⟶ g_*(ℱ_U/Iⁿℱ_U)`.  Assembled into a morphism of the short exact sequences of
the filtration, these run the induction of [Stacks, Tag 0E3X]: if `c_1` is invertible — the tag's
hypothesis `f_*𝒪_X = 𝒪_Y`, read on the special fibre — and `R¹g_*` kills the special fibre — the
tag's `R¹f_*𝒪_X = 0` — then every `c_n` is invertible, and over an Artinian local base `φ` itself
is.

At each `n` there are two short exact sequences, the filtration sequence of `ℱ_V` and the direct
image of the filtration sequence of `ℱ_U`:

```
0 ⟶ Iⁿ(ℱ_V/Iⁿ⁺¹ℱ_V) ⟶ ℱ_V/Iⁿ⁺¹ℱ_V ⟶ ℱ_V/Iⁿℱ_V ⟶ 0
0 ⟶ g_*(Iⁿ(ℱ_U/Iⁿ⁺¹ℱ_U)) ⟶ g_*(ℱ_U/Iⁿ⁺¹ℱ_U) ⟶ g_*(ℱ_U/Iⁿℱ_U) ⟶ 0
```

the second being short exact exactly because `R¹g_*` kills the graded piece
(`Stacks.BaseAdicFiltration.shortExact_map_pushforward_gradedShortComplex`).
`CategoryTheory.ShortComplex.isIso₂_of_shortExact_of_isIso₁₃'` then gets `c_{n+1}` from `c_n` and
from the map on graded pieces, so the whole induction rests on the graded pieces, which is where
the hypothesis on `c_1` is spent.

The map on graded pieces is not constructed by hand: the second sequence is short exact, so its
first map is a kernel of its second, and the restriction of `c_{n+1}` to the graded piece is the
induced map into that kernel.

Both graded pieces are computed by `Stacks.BaseAdicFiltration.gradedDesc`, whose input is a tuple
`a : Fin k → A` of representatives of a basis of `Iⁿ/Iⁿ⁺¹`.  That tuple comes from
`Stacks.Flatness.exists_pi_linearEquiv_gradedPiece I n`, which depends only on `(A, I, n)` and
not on the scheme or the module, so one choice serves `ℱ_V` on `V` and `ℱ_U` on `U` at once, and
the square

```
⨁_{i<k} ℱ_V/Iℱ_V  ⟶  Iⁿ(ℱ_V/Iⁿ⁺¹ℱ_V)
      |                        |
⨁_{i<k} g_*(ℱ_U/Iℱ_U)  ⟶  g_*(Iⁿ(ℱ_U/Iⁿ⁺¹ℱ_U))
```

with vertical maps `⨁ c_1` and the graded comparison commutes.

Commutativity of that square reduces, component by component, to the defining property of
`Stacks.Algebraization.idealPowerComponent` — each component is multiplication by `a i`
(`Stacks.Algebraization.comp_idealPowerComponent_comp_ι`) — together with two facts about
multiplication by a global function coming from the base:
`Stacks.BaseAdicFiltration.pushforward_sectionSmul`, that the direct image of multiplication by
the function on `U` is multiplication by the function on `V`, and
`Stacks.BaseAdicFiltration.sectionSmul_naturality`, that multiplication by a function is natural.

## Main definitions

* `Stacks.BaseAdicFiltration.gradedPieceComparison` — the map
  `Iⁿ(ℱ_V/Iⁿ⁺¹ℱ_V) ⟶ g_*(Iⁿ(ℱ_U/Iⁿ⁺¹ℱ_U))`.
* `Stacks.BaseAdicFiltration.gradedShortComplexComparison` — the morphism of short complexes.

## Main results

* `Stacks.BaseAdicFiltration.isIso_gradedDesc` — the graded piece is computed by a *given* tuple
  of representatives.
* `Stacks.BaseAdicFiltration.isIso_gradedPieceComparison` — the map on graded pieces is
  invertible once `c_1` is.
* `Stacks.BaseAdicFiltration.isIso_adicQuotientComparison_succ` — **the induction**: every `c_n`,
  `n ≥ 1`, is invertible.
* `Stacks.BaseAdicFiltration.isIso_of_isIso_adicQuotientComparison_one` — **the conclusion**:
  over an Artinian local base `φ` itself is invertible.

## References

* [Stacks Project, Tag 0E3X](https://stacks.math.columbia.edu/tag/0E3X)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Algebraization Stacks.AlgebraicGeometry.PushforwardIdealSubsheaf
open Stacks.AlgebraicGeometry.SectionsColimit
open scoped AlgebraicGeometry

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.BaseAdicFiltration

attribute [local instance] hasFiniteBiproducts_schemeModules

/-! ### Multiplication by a global function: naturality and direct images -/

/-- **Multiplication by a global function is natural.**  It is the component at `ℳ` of an
endomorphism of the identity functor (`Stacks.RegularSequence.globalSmulCenter`), so this is that
transformation's naturality. -/
theorem sectionSmul_naturality {X : Scheme.{u}} (b : Γ(X, ⊤)) {M N : X.Modules} (ψ : M ⟶ N) :
    sectionSmul b M ≫ ψ = ψ ≫ sectionSmul b N :=
  ((Stacks.RegularSequence.globalSmulCenter X b).naturality ψ).symm

section Functorial

variable {A : Type u} [CommRing A] {U V : Scheme.{u}}
  (pV : V ⟶ Spec (CommRingCat.of A)) {pU : U ⟶ Spec (CommRingCat.of A)} {g : U ⟶ V}
  (hg : g ≫ pV = pU)

include hg in
/-- **The direct image of multiplication by the function `a : A` determines on `U` is
multiplication by the function it determines on `V`.**  Both act on the sections over `W` of the
direct image — that is, on the sections of `𝒩` over `g ⁻¹ᵁ W` — by the restriction there of the
function on `U`, the one through `g` by
`Stacks.BaseAdicFiltration.app_map_baseScalarMap`. -/
theorem pushforward_sectionSmul (a : A) (N : U.Modules) :
    (Scheme.Modules.pushforward g).map (sectionSmul (baseScalarMap pU a) N) =
      sectionSmul (baseScalarMap pV a) ((Scheme.Modules.pushforward g).obj N) := by
  refine Scheme.Modules.hom_ext _ _ fun W => ?_
  ext x
  refine Eq.trans (sectionSmul_app (baseScalarMap pU a) N (g ⁻¹ᵁ W)
    (show Γ(N, g ⁻¹ᵁ W) from x)) ?_
  refine Eq.trans ?_ (sectionSmul_app (baseScalarMap pV a)
    ((Scheme.Modules.pushforward g).obj N) W x).symm
  refine Eq.trans (congrArg (fun r : Γ(U, g ⁻¹ᵁ W) => r • (show Γ(N, g ⁻¹ᵁ W) from x))
    (app_map_baseScalarMap pV hg W a)).symm ?_
  exact pushforward_app_smul g N W _ x

end Functorial

/-! ### The projection onto the special fibre -/

section SpecialFibreProj

variable {A : Type u} [CommRing A] {U : Scheme.{u}} (p : U ⟶ Spec (CommRingCat.of A))
  (I : Ideal A) (n : ℕ) (F : U.Modules) [F.IsQuasicoherent]

/-- The projection `ℱ/Iⁿ⁺¹ℱ ⟶ ℱ/Iℱ` onto the special fibre, named as the composite that
`Stacks.Algebraization.comp_idealPowerComponent_comp_ι` asks for: the `I`-projection of
`ℱ/Iⁿ⁺¹ℱ` followed by `Stacks.BaseAdicFiltration.specialFibreIso`. -/
def specialFibreProj : adicQuotient p I (n + 1) F ⟶ specialFibre p I F :=
  adicProj p I 1 (adicQuotient p I (n + 1) F) ≫ (specialFibreIso p I n F).1.hom

/-- The two projections out of `ℱ` compose to the projection onto the special fibre. -/
@[reassoc]
theorem adicProj_comp_specialFibreProj :
    adicProj p I (n + 1) F ≫ specialFibreProj p I n F = adicProj p I 1 F :=
  (specialFibreIso p I n F).2

/-- The projection onto the special fibre is an epimorphism. -/
instance epi_specialFibreProj : Epi (C := U.Modules) (specialFibreProj p I n F) := by
  have : IsIso (C := U.Modules) (specialFibreIso p I n F).1.hom :=
    inferInstanceAs (IsIso (C := U.Modules) (Iso.hom _))
  change Epi (C := U.Modules)
    (adicProj p I 1 (adicQuotient p I (n + 1) F) ≫ (specialFibreIso p I n F).1.hom)
  infer_instance

/-- The second map of `Stacks.BaseAdicFiltration.gradedShortComplex` is the projection
`ℱ/Iⁿ⁺¹ℱ ⟶ ℱ/Iⁿℱ`: its composite with the projection out of `ℱ` is that of `ℱ`. -/
theorem adicProj_comp_gradedShortComplex_g :
    adicProj p I (n + 1) F ≫ (gradedShortComplex p I n F).g = adicProj p I n F :=
  (adicQuotientIso p I n F).2

end SpecialFibreProj

/-! ### The graded piece is computed by a given tuple of representatives -/

/-- **`Stacks.BaseAdicFiltration.exists_isIso_gradedDesc` with the tuple supplied rather than
chosen.**  Given a `κ`-basis of `Iⁿ/Iⁿ⁺¹` and representatives of its members, multiplication by
those representatives is an isomorphism `⨁_{i<k} ℱ/Iℱ ≅ Iⁿ(ℱ/Iⁿ⁺¹ℱ)`. -/
theorem isIso_gradedDesc {A : Type u} [CommRing A] {U : Scheme.{u}}
    (p : U ⟶ Spec (CommRingCat.of A)) (I : Ideal A) (n : ℕ) (F : U.Modules)
    [F.IsQuasicoherent] [IsNoetherianRing A] [I.IsMaximal] (hflat : FlatStalks p F)
    {k : ℕ} (e₀ : (↥(I ^ n) ⧸ (I • (⊤ : Submodule A ↥(I ^ n)))) ≃ₗ[A] (Fin k → (A ⧸ I)))
    (rep : Fin k → ↥(I ^ n))
    (hrep : ∀ i, e₀.symm (Pi.single i (1 : A ⧸ I)) = Submodule.Quotient.mk (rep i))
    (e : adicQuotient p I 1 (adicQuotient p I (n + 1) F) ≅ specialFibre p I F)
    (he : adicProj p I (n + 1) F ≫ adicProj p I 1 (adicQuotient p I (n + 1) F) ≫ e.hom =
      adicProj p I 1 F) :
    IsIso (C := U.Modules) (gradedDesc p I n F (fun i => (rep i : A)) (fun i => (rep i).2) e) := by
  refine AlgebraicGeometry.isIso_of_forall_modulesStalk _ fun x => ?_
  rw [ConcreteCategory.isIso_iff_bijective]
  exact bijective_stalk_gradedDesc p I n F hflat e₀ rep hrep e he x

/-! ### The comparison of the filtration sequences -/

section Comparison

variable {A : Type u} [CommRing A] {U V : Scheme.{u}}
  (pV : V ⟶ Spec (CommRingCat.of A)) {pU : U ⟶ Spec (CommRingCat.of A)} {g : U ⟶ V}
  (hg : g ≫ pV = pU) (I : Ideal A) (n : ℕ)
  {FV : V.Modules} {FU : U.Modules} [FV.IsQuasicoherent] [FU.IsQuasicoherent]
  (φ : FV ⟶ (Scheme.Modules.pushforward g).obj FU)

include hg in
/-- **The comparison maps are compatible with the projections onto the special fibre.**  Both
sides become `φ` followed by the direct image of the projection `ℱ_U ⟶ ℱ_U/Iℱ_U` after
precomposition with the projection out of `ℱ_V`, which is an epimorphism. -/
@[reassoc]
theorem specialFibreProj_comp_adicQuotientComparison :
    specialFibreProj pV I n FV ≫ adicQuotientComparison pV hg I 1 φ =
      adicQuotientComparison pV hg I (n + 1) φ ≫
        (Scheme.Modules.pushforward g).map (specialFibreProj pU I n FU) := by
  refine (cancel_epi (adicProj pV I (n + 1) FV)).1 ?_
  rw [adicProj_comp_specialFibreProj_assoc, adicProj_comp_adicQuotientComparison,
    adicProj_comp_adicQuotientComparison_assoc, ← Functor.map_comp,
    adicProj_comp_specialFibreProj]

include hg in
/-- **The comparison maps are compatible with the second map of the filtration sequence.**  This
is the `comm₂₃` of the morphism of short complexes below. -/
theorem adicQuotientComparison_comm :
    adicQuotientComparison pV hg I (n + 1) φ ≫
        (Scheme.Modules.pushforward g).map ((gradedShortComplex pU I n FU).g) =
      (gradedShortComplex pV I n FV).g ≫ adicQuotientComparison pV hg I n φ := by
  refine (cancel_epi (adicProj pV I (n + 1) FV)).1 ?_
  have hmc := (Scheme.Modules.pushforward g).map_comp (adicProj pU I (n + 1) FU)
    (gradedShortComplex pU I n FU).g
  rw [adicProj_comp_gradedShortComplex_g] at hmc
  rw [adicProj_comp_adicQuotientComparison_assoc, ← hmc]
  exact (adicProj_comp_adicQuotientComparison pV hg I n φ).symm.trans
    ((congrArg (· ≫ adicQuotientComparison pV hg I n φ)
      (adicProj_comp_gradedShortComplex_g pV I n FV)).symm.trans (Category.assoc _ _ _))

variable (hSEU : ((gradedShortComplex pU I n FU).map
  (Scheme.Modules.pushforward g)).ShortExact)

include hg hSEU in
/-- The composite `Iⁿ(ℱ_V/Iⁿ⁺¹ℱ_V) ⟶ ℱ_V/Iⁿ⁺¹ℱ_V ⟶ g_*(ℱ_U/Iⁿ⁺¹ℱ_U)` lands in the kernel of the
second map of the direct image sequence. -/
theorem gradedShortComplex_f_comp_comparison_comp_g :
    ((gradedShortComplex pV I n FV).f ≫ adicQuotientComparison pV hg I (n + 1) φ) ≫
      ((gradedShortComplex pU I n FU).map (Scheme.Modules.pushforward g)).g = 0 := by
  show ((gradedShortComplex pV I n FV).f ≫ adicQuotientComparison pV hg I (n + 1) φ) ≫
      (Scheme.Modules.pushforward g).map ((gradedShortComplex pU I n FU).g) = 0
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun ψ => (gradedShortComplex pV I n FV).f ≫ ψ)
    (adicQuotientComparison_comm pV hg I n φ)) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun ψ => ψ ≫ adicQuotientComparison pV hg I n φ)
    (gradedShortComplex pV I n FV).zero) ?_
  exact zero_comp

include hg in
/-- **The comparison of the graded pieces**, `Iⁿ(ℱ_V/Iⁿ⁺¹ℱ_V) ⟶ g_*(Iⁿ(ℱ_U/Iⁿ⁺¹ℱ_U))`.

Nothing is constructed: the direct image sequence is short exact, so its first map is a kernel of
its second, and the restriction of `c_{n+1}` to the graded piece is the induced map into that
kernel. -/
def gradedPieceComparison :
    (gradedShortComplex pV I n FV).X₁ ⟶
      ((gradedShortComplex pU I n FU).map (Scheme.Modules.pushforward g)).X₁ :=
  haveI := hSEU.mono_f
  hSEU.exact.lift ((gradedShortComplex pV I n FV).f ≫ adicQuotientComparison pV hg I (n + 1) φ)
    (gradedShortComplex_f_comp_comparison_comp_g pV hg I n φ hSEU)

include hg in
/-- The comparison of the graded pieces is compatible with their inclusions: this is `comm₁₂` of
the morphism of short complexes, and it is `CategoryTheory.ShortComplex.Exact.lift_f`. -/
theorem gradedPieceComparison_comp_f :
    gradedPieceComparison pV hg I n φ hSEU ≫
        ((gradedShortComplex pU I n FU).map (Scheme.Modules.pushforward g)).f =
      (gradedShortComplex pV I n FV).f ≫ adicQuotientComparison pV hg I (n + 1) φ :=
  have := hSEU.mono_f
  hSEU.exact.lift_f _ _

include hg in
/-- **The morphism of short complexes** from the filtration sequence of `ℱ_V` to the direct image
of the filtration sequence of `ℱ_U`. -/
def gradedShortComplexComparison :
    gradedShortComplex pV I n FV ⟶
      (gradedShortComplex pU I n FU).map (Scheme.Modules.pushforward g) :=
  ShortComplex.homMk (gradedPieceComparison pV hg I n φ hSEU)
    (adicQuotientComparison pV hg I (n + 1) φ) (adicQuotientComparison pV hg I n φ)
    (gradedPieceComparison_comp_f pV hg I n φ hSEU)
    (adicQuotientComparison_comm pV hg I n φ)

include hg in
/-- `Stacks.BaseAdicFiltration.gradedPieceComparison_comp_f` with the inclusions written out
rather than named through the fields of the short complexes. -/
theorem gradedPieceComparison_comp_map_ι :
    gradedPieceComparison pV hg I n φ hSEU ≫
        (Scheme.Modules.pushforward g).map ((gradedPiece pU I n FU).ι) =
      (gradedPiece pV I n FV).ι ≫ adicQuotientComparison pV hg I (n + 1) φ :=
  gradedPieceComparison_comp_f pV hg I n φ hSEU

include hg hSEU in
/-- **The square of the comparison commutes, one component at a time.**  Let `ρ` and `ρ'` be maps
of the special fibre into the graded piece, on `V` and on `U`, each of which becomes
multiplication by one and the same `a : A` after composing with the projection onto the special
fibre and the inclusion of the graded piece.  Then `ρ` followed by the comparison of graded pieces
is the comparison of special fibres followed by the direct image of `ρ'`.

Both sides are tested after the inclusion of the graded piece on `U`, a monomorphism because the
direct image sequence is short exact, and before the projection onto the special fibre on `V`, an
epimorphism; they then become
multiplication by `a` on `ℱ_V/Iⁿ⁺¹ℱ_V` followed by `c_{n+1}`, and `c_{n+1}` followed by
multiplication by `a` on `g_*(ℱ_U/Iⁿ⁺¹ℱ_U)`, which agree because multiplication by a global
function is natural. -/
theorem comp_gradedPieceComparison_of_comp_ι (a : A)
    {ρ : specialFibre pV I FV ⟶ ((gradedPiece pV I n FV).toSheafOfModules : V.Modules)}
    {ρ' : specialFibre pU I FU ⟶ ((gradedPiece pU I n FU).toSheafOfModules : U.Modules)}
    (hρ : specialFibreProj pV I n FV ≫ ρ ≫ (gradedPiece pV I n FV).ι =
      sectionSmul (baseScalarMap pV a) (adicQuotient pV I (n + 1) FV))
    (hρ' : specialFibreProj pU I n FU ≫ ρ' ≫ (gradedPiece pU I n FU).ι =
      sectionSmul (baseScalarMap pU a) (adicQuotient pU I (n + 1) FU)) :
    ρ ≫ gradedPieceComparison pV hg I n φ hSEU =
      adicQuotientComparison pV hg I 1 φ ≫ (Scheme.Modules.pushforward g).map ρ' := by
  have : Mono (C := V.Modules)
      ((Scheme.Modules.pushforward g).map ((gradedPiece pU I n FU).ι)) := hSEU.mono_f
  have hmcU := (Scheme.Modules.pushforward g).map_comp ρ' (gradedPiece pU I n FU).ι
  have hmcS := (Scheme.Modules.pushforward g).map_comp (specialFibreProj pU I n FU)
    (ρ' ≫ (gradedPiece pU I n FU).ι)
  have hlhs : specialFibreProj pV I n FV ≫ (ρ ≫ gradedPieceComparison pV hg I n φ hSEU) ≫
        (Scheme.Modules.pushforward g).map ((gradedPiece pU I n FU).ι) =
      sectionSmul (baseScalarMap pV a) (adicQuotient pV I (n + 1) FV) ≫
        adicQuotientComparison pV hg I (n + 1) φ := by
    refine Eq.trans (congrArg (fun ψ => specialFibreProj pV I n FV ≫ ψ)
      (Category.assoc ρ (gradedPieceComparison pV hg I n φ hSEU)
        ((Scheme.Modules.pushforward g).map ((gradedPiece pU I n FU).ι)))) ?_
    refine Eq.trans (congrArg (fun ψ => specialFibreProj pV I n FV ≫ ρ ≫ ψ)
      (gradedPieceComparison_comp_map_ι pV hg I n φ hSEU)) ?_
    refine Eq.trans (congrArg (fun ψ => specialFibreProj pV I n FV ≫ ψ)
      (Category.assoc ρ ((gradedPiece pV I n FV).ι)
        (adicQuotientComparison pV hg I (n + 1) φ)).symm) ?_
    refine Eq.trans (Category.assoc (specialFibreProj pV I n FV)
      (ρ ≫ (gradedPiece pV I n FV).ι) (adicQuotientComparison pV hg I (n + 1) φ)).symm ?_
    exact congrArg (fun ψ => ψ ≫ adicQuotientComparison pV hg I (n + 1) φ) hρ
  have hrhs : specialFibreProj pV I n FV ≫ (adicQuotientComparison pV hg I 1 φ ≫
        (Scheme.Modules.pushforward g).map ρ') ≫
        (Scheme.Modules.pushforward g).map ((gradedPiece pU I n FU).ι) =
      adicQuotientComparison pV hg I (n + 1) φ ≫
        sectionSmul (baseScalarMap pV a) ((Scheme.Modules.pushforward g).obj
          (adicQuotient pU I (n + 1) FU)) := by
    refine Eq.trans (congrArg (fun ψ => specialFibreProj pV I n FV ≫ ψ)
      (Category.assoc (adicQuotientComparison pV hg I 1 φ)
        ((Scheme.Modules.pushforward g).map ρ')
        ((Scheme.Modules.pushforward g).map ((gradedPiece pU I n FU).ι)))) ?_
    refine Eq.trans (congrArg (fun ψ => specialFibreProj pV I n FV ≫
      adicQuotientComparison pV hg I 1 φ ≫ ψ) hmcU.symm) ?_
    refine Eq.trans (Category.assoc (specialFibreProj pV I n FV)
      (adicQuotientComparison pV hg I 1 φ)
      ((Scheme.Modules.pushforward g).map (ρ' ≫ (gradedPiece pU I n FU).ι))).symm ?_
    refine Eq.trans (congrArg
      (fun ψ => ψ ≫ (Scheme.Modules.pushforward g).map (ρ' ≫ (gradedPiece pU I n FU).ι))
      (specialFibreProj_comp_adicQuotientComparison pV hg I n φ)) ?_
    refine Eq.trans (Category.assoc (adicQuotientComparison pV hg I (n + 1) φ)
      ((Scheme.Modules.pushforward g).map (specialFibreProj pU I n FU))
      ((Scheme.Modules.pushforward g).map (ρ' ≫ (gradedPiece pU I n FU).ι))) ?_
    refine Eq.trans (congrArg
      (fun ψ => adicQuotientComparison pV hg I (n + 1) φ ≫ ψ) hmcS.symm) ?_
    refine Eq.trans (congrArg (fun ψ => adicQuotientComparison pV hg I (n + 1) φ ≫
      (Scheme.Modules.pushforward g).map ψ) hρ') ?_
    exact congrArg (fun ψ => adicQuotientComparison pV hg I (n + 1) φ ≫ ψ)
      (pushforward_sectionSmul pV hg a (adicQuotient pU I (n + 1) FU))
  refine (cancel_mono (C := V.Modules) ((Scheme.Modules.pushforward g).map
    ((gradedPiece pU I n FU).ι))).1 ?_
  refine (cancel_epi (C := V.Modules) (specialFibreProj pV I n FV)).1 ?_
  exact hlhs.trans ((sectionSmul_naturality _ _).trans hrhs.symm)

include hg hSEU in
/-- **Each component of the comparison square commutes**, for the components of
`Stacks.BaseAdicFiltration.gradedDesc`: multiplication by `a ∈ Iⁿ` into the graded piece. -/
theorem idealPowerComponent_comp_gradedPieceComparison {a : A} (ha : a ∈ I ^ n) :
    idealPowerComponent (adicQuotient pV I (n + 1) FV) n
          (adicFiltration_adicQuotient_eq_bot pV I n FV)
          (fun W => restrictMemIdealPow_baseScalarMap pV n ha W)
          (specialFibreIso pV I n FV).1 ≫
        gradedPieceComparison pV hg I n φ hSEU =
      adicQuotientComparison pV hg I 1 φ ≫
        (Scheme.Modules.pushforward g).map
          (idealPowerComponent (adicQuotient pU I (n + 1) FU) n
            (adicFiltration_adicQuotient_eq_bot pU I n FU)
            (fun W => restrictMemIdealPow_baseScalarMap pU n ha W)
            (specialFibreIso pU I n FU).1) :=
  comp_gradedPieceComparison_of_comp_ι pV hg I n φ hSEU a
    (comp_idealPowerComponent_comp_ι (adicQuotient pV I (n + 1) FV) n
      (adicFiltration_adicQuotient_eq_bot pV I n FV)
      (fun W => restrictMemIdealPow_baseScalarMap pV n ha W)
      (specialFibreIso pV I n FV).1 (t := specialFibreProj pV I n FV) rfl)
    (comp_idealPowerComponent_comp_ι (adicQuotient pU I (n + 1) FU) n
      (adicFiltration_adicQuotient_eq_bot pU I n FU)
      (fun W => restrictMemIdealPow_baseScalarMap pU n ha W)
      (specialFibreIso pU I n FU).1 (t := specialFibreProj pU I n FU) rfl)

include hg hSEU in
/-- **The square of the graded comparisons commutes.**  For a tuple `rep` of elements of `Iⁿ`, the
comparison `⨁_{i<k} ℱ_V/Iℱ_V ⟶ Iⁿ(ℱ_V/Iⁿ⁺¹ℱ_V)` given by multiplication by the `rep i` followed
by the comparison of graded pieces is `⨁ c_1` followed by the direct image of the corresponding
comparison on `U`.  Componentwise this is
`Stacks.BaseAdicFiltration.idealPowerComponent_comp_gradedPieceComparison`. -/
private theorem gradedDesc_comp_gradedPieceComparison
    [IsIso (adicQuotientComparison pV hg I 1 φ)] {k : ℕ} (rep : Fin k → ↥(I ^ n)) :
    gradedDesc pV I n FV (fun i => (rep i : A)) (fun i => (rep i).2)
          (specialFibreIso pV I n FV).1 ≫ gradedPieceComparison pV hg I n φ hSEU =
      (biproduct.mapIso (C := V.Modules) fun _ : Fin k =>
          asIso (adicQuotientComparison pV hg I 1 φ)).hom ≫
        ((Scheme.Modules.pushforward g).mapBiproduct
          (fun _ : Fin k => specialFibre pU I FU)).inv ≫
        (Scheme.Modules.pushforward g).map
          (gradedDesc pU I n FU (fun i => (rep i : A)) (fun i => (rep i).2)
            (specialFibreIso pU I n FU).1) := by
  classical
  refine biproduct.hom_ext' _ _ fun i => ?_
  -- the `i`-th component on the left is the `i`-th component of `gradedDesc`
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun ψ => ψ ≫ gradedPieceComparison pV hg I n φ hSEU)
    (biproduct.ι_desc (fun j => idealPowerComponent (adicQuotient pV I (n + 1) FV) n
      (adicFiltration_adicQuotient_eq_bot pV I n FV)
      (fun W => restrictMemIdealPow_baseScalarMap pV n (rep j).2 W)
      (specialFibreIso pV I n FV).1) i)) ?_
  refine Eq.trans (idealPowerComponent_comp_gradedPieceComparison pV hg I n φ hSEU
    (rep i).2) ?_
  -- and the `i`-th component on the right is `c₁` followed by the direct image of it
  refine Eq.trans ?_ (Category.assoc _ _ _)
  refine Eq.trans ?_ (congrArg (fun ψ => ψ ≫ ((((Scheme.Modules.pushforward g).mapBiproduct
        (fun _ : Fin k => specialFibre pU I FU)).inv) ≫
      (Scheme.Modules.pushforward g).map
        (gradedDesc pU I n FU (fun j => (rep j : A)) (fun j => (rep j).2)
          (specialFibreIso pU I n FU).1)))
    (biproduct.ι_map (fun _ : Fin k =>
      (asIso (adicQuotientComparison pV hg I 1 φ)).hom) i)).symm
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  refine congrArg (fun ψ => adicQuotientComparison pV hg I 1 φ ≫ ψ) ?_
  refine Eq.trans ?_ (congrArg (fun ψ => biproduct.ι
      (fun _ : Fin k => (Scheme.Modules.pushforward g).obj (specialFibre pU I FU)) i ≫ ψ)
    (biproduct.mapBiproduct_inv_map_desc (F := Scheme.Modules.pushforward g)
      (g := fun j => idealPowerComponent (adicQuotient pU I (n + 1) FU) n
        (adicFiltration_adicQuotient_eq_bot pU I n FU)
        (fun W => restrictMemIdealPow_baseScalarMap pU n (rep j).2 W)
        (specialFibreIso pU I n FU).1))).symm
  exact (biproduct.ι_desc (fun j => (Scheme.Modules.pushforward g).map
    (idealPowerComponent (adicQuotient pU I (n + 1) FU) n
      (adicFiltration_adicQuotient_eq_bot pU I n FU)
      (fun W => restrictMemIdealPow_baseScalarMap pU n (rep j).2 W)
      (specialFibreIso pU I n FU).1)) i).symm

include hg hSEU in
/-- **The comparison of graded pieces is invertible once the comparison of special fibres is.**
Both graded pieces are computed by multiplication by one and the same tuple of representatives of
a `κ`-basis of `Iⁿ/Iⁿ⁺¹` — the tuple depends only on `A`, `I` and `n`
(`Stacks.Flatness.exists_pi_linearEquiv_gradedPiece`), so one choice serves both schemes — and
the resulting square commutes componentwise by
`Stacks.BaseAdicFiltration.idealPowerComponent_comp_gradedPieceComparison`. -/
theorem isIso_gradedPieceComparison [IsNoetherianRing A] [I.IsMaximal]
    (hflatV : FlatStalks pV FV) (hflatU : FlatStalks pU FU)
    (h1 : IsIso (adicQuotientComparison pV hg I 1 φ)) :
    IsIso (gradedPieceComparison pV hg I n φ hSEU) := by
  classical
  have := h1
  obtain ⟨k, ⟨e₀⟩⟩ := Stacks.Flatness.exists_pi_linearEquiv_gradedPiece I n
  choose rep hrep using fun i : Fin k =>
    Submodule.Quotient.mk_surjective (I • (⊤ : Submodule A ↥(I ^ n)))
      (e₀.symm (Pi.single i (1 : A ⧸ I)))
  have : IsIso (C := V.Modules) (gradedDesc pV I n FV (fun i => (rep i : A))
      (fun i => (rep i).2) (specialFibreIso pV I n FV).1) :=
    isIso_gradedDesc pV I n FV hflatV e₀ rep (fun i => (hrep i).symm)
      (specialFibreIso pV I n FV).1 (specialFibreIso pV I n FV).2
  have : IsIso (C := U.Modules) (gradedDesc pU I n FU (fun i => (rep i : A))
      (fun i => (rep i).2) (specialFibreIso pU I n FU).1) :=
    isIso_gradedDesc pU I n FU hflatU e₀ rep (fun i => (hrep i).symm)
      (specialFibreIso pU I n FU).1 (specialFibreIso pU I n FU).2
  have hsq := gradedDesc_comp_gradedPieceComparison pV hg I n φ hSEU rep
  have : IsIso (C := V.Modules) ((biproduct.mapIso (C := V.Modules) fun _ : Fin k =>
      asIso (adicQuotientComparison pV hg I 1 φ)).hom) := Iso.isIso_hom _
  have : IsIso (C := V.Modules) (((Scheme.Modules.pushforward g).mapBiproduct
      (fun _ : Fin k => specialFibre pU I FU)).inv) := Iso.isIso_inv _
  have : IsIso (C := V.Modules) ((Scheme.Modules.pushforward g).map
      (gradedDesc pU I n FU (fun i => (rep i : A)) (fun i => (rep i).2)
        (specialFibreIso pU I n FU).1)) :=
    ((Scheme.Modules.pushforward g).mapIso (asIso (C := U.Modules)
      (gradedDesc pU I n FU (fun i => (rep i : A)) (fun i => (rep i).2)
        (specialFibreIso pU I n FU).1))).isIso_hom
  -- the right-hand side of `hsq` is the underlying morphism of an isomorphism
  have hE : (biproduct.mapIso (C := V.Modules) fun _ : Fin k =>
        asIso (adicQuotientComparison pV hg I 1 φ)).hom ≫
      ((Scheme.Modules.pushforward g).mapBiproduct
          (fun _ : Fin k => specialFibre pU I FU)).inv ≫
        (Scheme.Modules.pushforward g).map
          (gradedDesc pU I n FU (fun i => (rep i : A)) (fun i => (rep i).2)
            (specialFibreIso pU I n FU).1) =
      ((biproduct.mapIso (C := V.Modules) fun _ : Fin k =>
            asIso (adicQuotientComparison pV hg I 1 φ)) ≪≫
          ((Scheme.Modules.pushforward g).mapBiproduct
            (fun _ : Fin k => specialFibre pU I FU)).symm ≪≫
          (Scheme.Modules.pushforward g).mapIso (asIso (C := U.Modules)
            (gradedDesc pU I n FU (fun i => (rep i : A)) (fun i => (rep i).2)
              (specialFibreIso pU I n FU).1))).hom := rfl
  have : IsIso (C := V.Modules) (gradedDesc pV I n FV (fun i => (rep i : A))
      (fun i => (rep i).2) (specialFibreIso pV I n FV).1 ≫
      gradedPieceComparison pV hg I n φ hSEU) := by
    rw [hsq, hE]
    exact Iso.isIso_hom _
  exact IsIso.of_isIso_comp_left (C := V.Modules) (gradedDesc pV I n FV (fun i => (rep i : A))
    (fun i => (rep i).2) (specialFibreIso pV I n FV).1) _

end Comparison

/-! ### The induction up the filtration -/

section Induction

variable {A : Type u} [CommRing A] {U V : Scheme.{u}}
  (pV : V ⟶ Spec (CommRingCat.of A)) {pU : U ⟶ Spec (CommRingCat.of A)} {g : U ⟶ V}
  (hg : g ≫ pV = pU) (I : Ideal A)
  {FV : V.Modules} {FU : U.Modules} [FV.IsQuasicoherent] [FU.IsQuasicoherent]
  (φ : FV ⟶ (Scheme.Modules.pushforward g).obj FU)

include hg in
/-- **The induction of [Stacks, Tag 0E3X].**  If the comparison of special fibres is invertible
and `R¹g_*` kills the special fibre, then every comparison `ℱ_V/Iⁿℱ_V ⟶ g_*(ℱ_U/Iⁿℱ_U)` with
`n ≥ 1` is invertible.

The induction is on `n`, each step being
`CategoryTheory.ShortComplex.isIso₂_of_shortExact_of_isIso₁₃'` applied to
`Stacks.BaseAdicFiltration.gradedShortComplexComparison`: the outer terms are the graded piece,
handled by `Stacks.BaseAdicFiltration.isIso_gradedPieceComparison`, and the previous quotient,
handled by the inductive hypothesis. -/
theorem isIso_adicQuotientComparison_succ [IsNoetherianRing A] [I.IsMaximal]
    (hflatV : FlatStalks pV FV) (hflatU : FlatStalks pU FU)
    (h1 : IsIso (adicQuotientComparison pV hg I 1 φ))
    (hR : IsZero (((Scheme.Modules.pushforward g).rightDerived 1).obj
      (specialFibre pU I FU))) (m : ℕ) :
    IsIso (adicQuotientComparison pV hg I (m + 1) φ) := by
  induction m with
  | zero => exact h1
  | succ j ih =>
    have hSEU : ((gradedShortComplex pU I (j + 1) FU).map
        (Scheme.Modules.pushforward g)).ShortExact :=
      shortExact_map_pushforward_gradedShortComplex pU I (j + 1) FU g hflatU hR
    have hSEV : (gradedShortComplex pV I (j + 1) FV).ShortExact :=
      gradedShortComplex_shortExact pV I (j + 1) FV
    exact ShortComplex.isIso₂_of_shortExact_of_isIso₁₃'
      (gradedShortComplexComparison pV hg I (j + 1) φ hSEU) hSEV hSEU
      (isIso_gradedPieceComparison pV hg I (j + 1) φ hSEU hflatV hflatU h1) ih

include hg in
/-- **Over an Artinian local base the morphism itself is invertible.**  This is the conclusion of
the filtration argument of [Stacks, Tag 0E3X]: for `𝔪` the maximal ideal of an Artinian local
`A`, with `ℱ_V` and `ℱ_U` flat over `A` at every point, `φ : ℱ_V ⟶ g_* ℱ_U` is an isomorphism as
soon as

* the comparison of special fibres `ℱ_V/𝔪ℱ_V ⟶ g_*(ℱ_U/𝔪ℱ_U)` is an isomorphism — the tag's
  hypothesis `f_*𝒪_X = 𝒪_Y`; and
* `R¹g_*(ℱ_U/𝔪ℱ_U) = 0` — the tag's hypothesis `R¹f_*𝒪_X = 0`.

The filtration reaches zero because `𝔪` is nilpotent
(`Stacks.BaseAdicFiltration.adicFiltration_eq_bot`), so at a large enough exponent both
projections `ℱ ⟶ ℱ/𝔪ⁿℱ` are isomorphisms and the comparison at that exponent *is* `φ`. -/
theorem isIso_of_isIso_adicQuotientComparison_one [IsArtinianRing A] [IsLocalRing A]
    (hflatV : FlatStalks pV FV) (hflatU : FlatStalks pU FU)
    (h1 : IsIso (adicQuotientComparison pV hg (IsLocalRing.maximalIdeal A) 1 φ))
    (hR : IsZero (((Scheme.Modules.pushforward g).rightDerived 1).obj
      (specialFibre pU (IsLocalRing.maximalIdeal A) FU))) :
    IsIso φ := by
  obtain ⟨N, hN⟩ := (isArtinianRing_iff_isNilpotent_maximalIdeal A).1 ‹IsArtinianRing A›
  have hN' : (IsLocalRing.maximalIdeal A) ^ (N + 1) = ⊥ := by
    rw [pow_succ, hN, zero_mul]
    rfl
  have : IsIso (adicProj pV (IsLocalRing.maximalIdeal A) (N + 1) FV) :=
    isIso_cokernel_π_of_idealPowerMultiple_eq_bot _ _ _
      (adicFiltration_eq_bot pV FV hN')
  have : IsIso (adicProj pU (IsLocalRing.maximalIdeal A) (N + 1) FU) :=
    isIso_cokernel_π_of_idealPowerMultiple_eq_bot _ _ _
      (adicFiltration_eq_bot pU FU hN')
  have : IsIso (adicQuotientComparison pV hg (IsLocalRing.maximalIdeal A) (N + 1) φ) :=
    isIso_adicQuotientComparison_succ pV hg (IsLocalRing.maximalIdeal A) φ hflatV hflatU h1 hR N
  have : IsIso (φ ≫ (Scheme.Modules.pushforward g).map
      (adicProj pU (IsLocalRing.maximalIdeal A) (N + 1) FU)) := by
    rw [← adicProj_comp_adicQuotientComparison pV hg (IsLocalRing.maximalIdeal A) (N + 1) φ]
    infer_instance
  exact IsIso.of_isIso_comp_right φ ((Scheme.Modules.pushforward g).map
    (adicProj pU (IsLocalRing.maximalIdeal A) (N + 1) FU))

include hg in
/-- **The structure-sheaf case, which is the one [Stacks, Tag 0E3X] needs.**  For `p_V` and `p_U`
flat over an Artinian local base and `g : U ⟶ V` over it, a morphism
`φ : 𝒪_V ⟶ g_* 𝒪_U` of `𝒪_V`-modules is an isomorphism as soon as the comparison it induces on
special fibres is one and `R¹g_*` kills the special fibre.

Flatness of the two families is what `Stacks.BaseAdicFiltration.flatStalks_unit` turns into the
flatness of stalks the graded pieces ask for. -/
theorem isIso_structureSheafComparison_of_isIso_specialFibre [IsArtinianRing A] [IsLocalRing A]
    [AlgebraicGeometry.Flat pV] [AlgebraicGeometry.Flat pU]
    (φ : (SheafOfModules.unit V.ringCatSheaf : V.Modules) ⟶
      (Scheme.Modules.pushforward g).obj (SheafOfModules.unit U.ringCatSheaf))
    (h1 : IsIso (adicQuotientComparison pV hg (IsLocalRing.maximalIdeal A) 1 φ))
    (hR : IsZero (((Scheme.Modules.pushforward g).rightDerived 1).obj
      (specialFibre pU (IsLocalRing.maximalIdeal A) (SheafOfModules.unit U.ringCatSheaf)))) :
    IsIso (C := V.Modules) φ :=
  isIso_of_isIso_adicQuotientComparison_one pV hg φ (flatStalks_unit pV) (flatStalks_unit pU)
    h1 hR

end Induction

end Stacks.BaseAdicFiltration

end
