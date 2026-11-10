module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.PoincareDualityInduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.LocalPurity
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-!
# Existence of good traces

Let `k` be an algebraically closed field, `ℓ` a prime and `Λ = ℤ/ℓ`. For `W` smooth irreducible
of relative dimension `e` over `k` with a compactification `j : W → X̄`, every injective trace
`t : H^{2e}_c(W) = Ext^{2e}_X̄(Λ, j_! Λ_W) → Λ` is good (`Stacks.EtaleCohomology.IsGoodTrace`):
the trace `stratumTrace` it induces on `H^{2e'}_c(T)`, for every smooth irreducible stratum `T`
closed in an open of `W` with a purity class `γ`, is again injective.

This rests on two inputs. *Local purity* (`Stacks.EtaleCohomology.Purity.localPurity`, for `ℓ`
invertible in `k`) provides, at a closed point `x` of `T`, a purity class `δ` of `x` in an open
`N'` of `T`. The computation of the top compactly supported cohomology
(`Stacks.EtaleCohomology.TopCohomologyPointClass`, Stacks' `H^{2e}_c(W) ≅ Λ`) says that the class
of a point generates it freely. The Gysin class of `γ` sends the class of `x` in `T` to a class of
`x` in `W`: the composite of the Gysin classes of `δ` and `γ` comes from a purity class `ε` of `x`
in the open `N` of `W`, because purity classes compose (`y ↦ ι_* y ∘ Γ_γ` is a bijection on
`Ext(u_! G, u_! Λ_T)`, `Stacks.EtaleCohomology.bijective_mapExactFunctor_comp_stratumGysinClass`).
So the Gysin map `H^{2e'}_c(T) → H^{2e}_c(W)`, which is the identity `Λ → Λ` on point classes, is
injective, and so is the induced trace (`Stacks.EtaleCohomology.injective_stratumTrace`).

## Main definitions

* `Stacks.EtaleCohomology.TopCohomologyPointClass`.

## Main results

* `Stacks.EtaleCohomology.injective_stratumTrace`.
* `Stacks.EtaleCohomology.isGoodTraceAux_of_injective`.
* `Stacks.EtaleCohomology.isGoodTrace_of_injective`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open Stacks.EtaleCohomology.ExtensionTorsor

universe u

namespace Stacks.ExtAdjunction

variable {C : Type*} [Category C] [Abelian C] {D : Type*} [Category D] [Abelian D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) [L.Additive] [PreservesFiniteLimits L]
  [PreservesFiniteColimits L] [HasExt.{u} C] [HasExt.{u} D]

/-- The adjunction map `Ext(A, R M) → Ext(L A, M)` is compatible with the Yoneda product on the
left: `(y ∘ γ)♭ = L(y) ∘ γ♭`. -/
theorem extMap_comp {A' A : C} {M : D} {q c q' : ℕ} (y : Ext.{u} A' A q)
    (γ : Ext.{u} A (R.obj M) c) (h : q + c = q') :
    extMap adj A' M q' (y.comp γ h) = (y.mapExactFunctor L).comp (extMap adj A M c γ) h := by
  rw [extMap_apply, extMap_apply, Ext.mapExactFunctor_comp]
  exact Ext.comp_assoc _ _ _ h (add_zero c) (by omega)

end Stacks.ExtAdjunction

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize comp_preservesFiniteLimits
  comp_preservesFiniteColimits

-- `Scheme.etaleSheaves_enoughInjectives` leaves the module universe of `EtaleModules` free;
-- `etaleModules_enoughInjectives` is the same fact at the right universe.
attribute [-instance] AlgebraicGeometry.Scheme.etaleSheaves_enoughInjectives

section StratumGysin

variable {ℓ : ℕ} [Fact ℓ.Prime] {T W X Tb : Scheme.{u}} (i : T ⟶ W) (u : T ⟶ Tb) (j : W ⟶ X)
  (ι : Tb ⟶ X) [IsOpenImmersion j] [IsOpenImmersion u] [IsClosedImmersion ι]
  (sq : IsPullback i u j ι) (D : EtaleModules.{u, 0} (ZMod ℓ) X) {c : ℕ}
  [IsClosedImmersion i]
  [PreservesFiniteColimits (etaleModuleDirectImage.{u, 0} (ZMod ℓ) i)]
  [PreservesFiniteColimits (etaleModuleDirectImage.{u, 0} (ZMod ℓ) ι)]
  (γ : Ext ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj (unitSheaf (X := T) ℓ))
    ((etaleModuleRestriction.{u, 0} (ZMod ℓ) j).obj D) c)

/-- **The Gysin class of a purity class induces bijections on `Ext` from sheaves extended by
zero from the stratum.** For a purity class `γ` of `i : T → W` and `M ≅ u_! G` on `T̄`,
`w ↦ ι_* w ∘ Γ_γ : Ext^q_{T̄}(M, u_! Λ_T) → Ext^{q+c}_X̄(ι_* M, D)` is bijective: through
`u_!`, `j_! i_* ≅ ι_* u_!` and `j_! ⊣ j^{-1}` it is the purity bijection
`Ext^q_T(G, Λ_T) ≅ Ext^{q+c}_W(i_* G, j^{-1} D)`. -/
theorem bijective_mapExactFunctor_comp_stratumGysinClass (hγ : IsPurityClass i _ γ)
    {M : EtaleModules.{u, 0} (ZMod ℓ) Tb} (G : EtaleModules.{u, 0} (ZMod ℓ) T)
    (eM : M ≅ (etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) u).obj G) (q q' : ℕ) (h : q + c = q') :
    Function.Bijective (fun w : Ext M ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) u).obj
        (unitSheaf (X := T) ℓ)) q =>
      (w.mapExactFunctor (etaleModuleDirectImage.{u, 0} (ZMod ℓ) ι)).comp
        (stratumGysinClass i u j ι sq D γ) h) := by
  subst h
  let e := etaleModuleExtensionByZeroDirectImageIso.{u, 0} (ZMod ℓ) i u j ι sq
  let iS := etaleModuleDirectImage.{u, 0} (ZMod ℓ) i
  let jS := etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) j
  let uS := etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) u
  let ιS := etaleModuleDirectImage.{u, 0} (ZMod ℓ) ι
  have hU := Stacks.ExtAdjunction.mapExtAddHom_bijective
    (etaleModuleExtensionByZeroAdj.{u, 0} (ZMod ℓ) u) G (unitSheaf (X := T) ℓ) q
  let adjJ := etaleModuleExtensionByZeroAdj.{u, 0} (ZMod ℓ) j
  have key : ∀ y' : Ext G (unitSheaf (X := T) ℓ) q,
      ((y'.mapExactFunctor uS).mapExactFunctor ιS).comp (stratumGysinClass i u j ι sq D γ)
        (rfl : q + c = q + c) =
      (Ext.mk₀ (e.inv.app G)).comp (Stacks.ExtAdjunction.extMap adjJ (iS.obj G) D (q + c)
        ((y'.mapExactFunctor iS).comp γ (rfl : q + c = q + c))) (zero_add _) := by
    intro y'
    rw [stratumGysinClass, Stacks.ExtFunctorial.mapExactFunctor_comp_functor uS ιS G q y',
      ← Ext.comp_assoc_of_second_deg_zero,
      ← Stacks.ExtFunctorial.mk₀_comp_mapExactFunctor e.inv G q y',
      Ext.comp_assoc _ _ _ (zero_add q) rfl (by omega),
      ← Stacks.ExtFunctorial.mapExactFunctor_comp_functor iS jS G q y',
      Stacks.ExtAdjunction.extMap_apply, Stacks.ExtAdjunction.extMap_apply,
      Ext.mapExactFunctor_comp, Ext.comp_assoc_of_third_deg_zero]
  have hfun : ((fun y : Ext (uS.obj G) (uS.obj (unitSheaf (X := T) ℓ)) q =>
      (y.mapExactFunctor ιS).comp (stratumGysinClass i u j ι sq D γ) (rfl : q + c = q + c)) ∘
        ⇑(uS.mapExtAddHom G (unitSheaf (X := T) ℓ) q)) =
      (fun y => (Ext.mk₀ (e.inv.app G)).comp y (zero_add _)) ∘
        ⇑(Stacks.ExtAdjunction.extMap adjJ (iS.obj G) D (q + c)) ∘
        (fun y' : Ext G (unitSheaf (X := T) ℓ) q =>
          (y'.mapExactFunctor iS).comp γ (rfl : q + c = q + c)) := by
    funext y'
    exact key y'
  have hG : Function.Bijective (fun y : Ext (uS.obj G) (uS.obj (unitSheaf (X := T) ℓ)) q =>
      (y.mapExactFunctor ιS).comp (stratumGysinClass i u j ι sq D γ) (rfl : q + c = q + c)) := by
    rw [← Function.Bijective.of_comp_iff _ hU, hfun]
    exact (Stacks.ExtAdjunction.precomp_mk₀_bijective_of_isIso _ _).comp
      ((Stacks.ExtAdjunction.extMap_bijective adjJ (iS.obj G) D (q + c)).comp (hγ.1 G q))
  have hfun' : ((fun w : Ext M (uS.obj (unitSheaf (X := T) ℓ)) q =>
      (w.mapExactFunctor ιS).comp (stratumGysinClass i u j ι sq D γ) (rfl : q + c = q + c)) ∘
        (fun y => (Ext.mk₀ eM.hom).comp y (zero_add q))) =
      (fun y => (Ext.mk₀ (ιS.map eM.hom)).comp y (zero_add _)) ∘
        (fun y : Ext (uS.obj G) (uS.obj (unitSheaf (X := T) ℓ)) q =>
          (y.mapExactFunctor ιS).comp (stratumGysinClass i u j ι sq D γ)
            (rfl : q + c = q + c)) := by
    funext y
    simp only [Function.comp_apply]
    rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
      Ext.comp_assoc _ _ _ (zero_add q) rfl (by omega)]
  have hP : Function.Bijective (fun y : Ext (uS.obj G) (uS.obj (unitSheaf (X := T) ℓ)) q =>
      (Ext.mk₀ eM.hom).comp y (zero_add q)) :=
    Stacks.ExtAdjunction.precomp_mk₀_bijective_of_isIso eM.hom q
  rw [← Function.Bijective.of_comp_iff _ hP, hfun']
  exact (Stacks.ExtAdjunction.precomp_mk₀_bijective_of_isIso _ _).comp hG

include sq in
omit [PreservesFiniteColimits (etaleModuleDirectImage.{u, 0} (ZMod ℓ) i)]
  [PreservesFiniteColimits (etaleModuleDirectImage.{u, 0} (ZMod ℓ) ι)] in
/-- **`Ext` below the codimension vanishes at sheaves extended by zero from the stratum**: for a
purity class `γ` of degree `c` and `M ≅ u_! G` on `T̄`, `Ext^q_X̄(ι_* M, D) ≅ Ext^q_W(i_* G,
j^{-1} D) = 0` for `q < c`. -/
theorem subsingleton_ext_directImage_of_isPurityClass (hγ : IsPurityClass i _ γ)
    {M : EtaleModules.{u, 0} (ZMod ℓ) Tb} (G : EtaleModules.{u, 0} (ZMod ℓ) T)
    (eM : M ≅ (etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) u).obj G) (q : ℕ) (hq : q < c) :
    Subsingleton (Ext ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) ι).obj M) D q) := by
  have := hγ.2 G q hq
  have : Subsingleton (Ext ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) ι).obj
      ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) u).obj G)) D q) :=
    Function.Surjective.subsingleton (f := ⇑((Ext.mk₀
      ((etaleModuleExtensionByZeroDirectImageIso.{u, 0} (ZMod ℓ) i u j ι sq).inv.app G)).precomp
        D (zero_add q)) ∘
      ⇑(Stacks.ExtAdjunction.extMap (etaleModuleExtensionByZeroAdj.{u, 0} (ZMod ℓ) j)
        ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj G) D q))
      ((Stacks.ExtAdjunction.precomp_mk₀_bijective_of_isIso _ _).2.comp
        (Stacks.ExtAdjunction.extMap_bijective
          (etaleModuleExtensionByZeroAdj.{u, 0} (ZMod ℓ) j)
          ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj G) D q).2)
  exact (Stacks.ExtAdjunction.precomp_mk₀_bijective_of_isIso
    ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) ι).map eM.hom) q).2.subsingleton

section PointGysin

variable {N' P : Scheme.{u}} (a : N' ⟶ T) [IsOpenImmersion a] (i' : P ⟶ N')
  [IsClosedImmersion i'] [IsClosedImmersion (i' ≫ a)] [IsClosedImmersion (i' ≫ a ≫ i)]

/-- For a point `i' : P → N'` closed in an open `a : N' → T` and closed in `T`, the sheaves on `X`
extended from `P` through `N'`, `T`, `T̄` and through `N'`, `T`, `W` agree:
`j_! (i' ≫ a ≫ i)_* ≅ ι_* (a ≫ u)_! i'_*`. -/
def pointStratumDirectImageIso :
    etaleModuleDirectImage.{u, 0} (ZMod ℓ) (i' ≫ a ≫ i) ⋙
        etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) j ≅
      (etaleModuleDirectImage.{u, 0} (ZMod ℓ) i' ⋙
        etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) (a ≫ u)) ⋙
          etaleModuleDirectImage.{u, 0} (ZMod ℓ) ι :=
  Functor.isoWhiskerRight (etaleModuleDirectImageComp.{u, 0} (ZMod ℓ) (i' ≫ a) i (i' ≫ a ≫ i)
      (Category.assoc _ _ _).symm).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (etaleModuleExtensionByZeroDirectImageIso.{u, 0} (ZMod ℓ) i u j ι sq) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerRight ((Functor.leftUnitor _).symm ≪≫
        Functor.isoWhiskerRight (etaleModuleExtensionByZeroIdIso (ZMod ℓ) P).symm _ ≪≫
        (etaleModuleExtensionByZeroDirectImageIso.{u, 0} (ZMod ℓ) i' (𝟙 P) a (i' ≫ a)
          (IsPullback.of_vert_isIso_mono ⟨by simp⟩)).symm) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (etaleModuleExtensionByZeroCompIso.{u, 0} (ZMod ℓ) a u).symm) _

/-- **Gysin classes of purity classes compose.** Let `γ` be a purity class of degree `c` of the
stratum `i : T → W`, and `δ` a purity class of degree `d₁` of a point `i' : P → N'` closed in an
open `a : N' → T`, for `(a ≫ u)^{-1} u_! Λ_T`. A class `ε` of `P` in `W` whose Gysin class on `X`
is `ι_* Γ_δ ∘ Γ_γ` (through `pointStratumDirectImageIso`) is a purity class. -/
theorem isPurityClass_of_extMap_eq_stratumGysinClass {d₁ d : ℕ} (h : d₁ + c = d)
    (hγ : IsPurityClass i _ γ)
    (δ : Ext ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i').obj (unitSheaf (X := P) ℓ))
      ((etaleModuleRestriction.{u, 0} (ZMod ℓ) (a ≫ u)).obj
        ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) u).obj (unitSheaf (X := T) ℓ))) d₁)
    (hδ : IsPurityClass i' _ δ)
    (ε : Ext ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) (i' ≫ a ≫ i)).obj (unitSheaf (X := P) ℓ))
      ((etaleModuleRestriction.{u, 0} (ZMod ℓ) j).obj D) d)
    (hε : Stacks.ExtAdjunction.extMap (etaleModuleExtensionByZeroAdj.{u, 0} (ZMod ℓ) j) _ D d ε =
      (Ext.mk₀ ((pointStratumDirectImageIso (ℓ := ℓ) i u j ι sq a i').hom.app
          (unitSheaf (X := P) ℓ))).comp
        (((Stacks.ExtAdjunction.extMap (etaleModuleExtensionByZeroAdj.{u, 0} (ZMod ℓ) (a ≫ u))
          _ _ d₁ δ).mapExactFunctor (etaleModuleDirectImage.{u, 0} (ZMod ℓ) ι)).comp
            (stratumGysinClass i u j ι sq D γ) h) (zero_add d)) :
    IsPurityClass (i' ≫ a ≫ i) _ ε := by
  let Ψ := pointStratumDirectImageIso (ℓ := ℓ) i u j ι sq a i'
  let iS' := etaleModuleDirectImage.{u, 0} (ZMod ℓ) i'
  let vS := etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) (a ≫ u)
  let uS := etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) u
  let ιS := etaleModuleDirectImage.{u, 0} (ZMod ℓ) ι
  let jS := etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) j
  let i''S := etaleModuleDirectImage.{u, 0} (ZMod ℓ) (i' ≫ a ≫ i)
  let adjJ := etaleModuleExtensionByZeroAdj.{u, 0} (ZMod ℓ) j
  let adjV := etaleModuleExtensionByZeroAdj.{u, 0} (ZMod ℓ) (a ≫ u)
  let Γs := stratumGysinClass i u j ι sq D γ
  let eM := fun G => (etaleModuleExtensionByZeroCompIso.{u, 0} (ZMod ℓ) a u).app (iS'.obj G)
  refine ⟨fun G q => ?_, fun G q hq => ?_⟩
  · rw [← Function.Bijective.of_comp_iff'
      (Stacks.ExtAdjunction.extMap_bijective adjJ (i''S.obj G) D (q + d))]
    have hfun : (⇑(Stacks.ExtAdjunction.extMap adjJ (i''S.obj G) D (q + d)) ∘
        fun y₀ : Ext G (unitSheaf (X := P) ℓ) q => (y₀.mapExactFunctor i''S).comp ε rfl) =
        (fun w => (Ext.mk₀ (Ψ.hom.app G)).comp w (zero_add _)) ∘
        (fun w : Ext (vS.obj (iS'.obj G)) (uS.obj (unitSheaf (X := T) ℓ)) (q + d₁) =>
          (w.mapExactFunctor ιS).comp Γs (show q + d₁ + c = q + d by omega)) ∘
        ⇑(Stacks.ExtAdjunction.extMap adjV (iS'.obj G) (uS.obj (unitSheaf (X := T) ℓ))
          (q + d₁)) ∘
        (fun y₀ : Ext G (unitSheaf (X := P) ℓ) q => (y₀.mapExactFunctor iS').comp δ rfl) := by
      funext y₀
      simp only [Function.comp_apply]
      rw [Stacks.ExtAdjunction.extMap_comp, hε, Stacks.ExtAdjunction.extMap_comp,
        Ext.mapExactFunctor_comp, Stacks.ExtFunctorial.mapExactFunctor_comp_functor i''S jS,
        ← Ext.comp_assoc_of_second_deg_zero,
        ← Stacks.ExtFunctorial.mk₀_comp_mapExactFunctor Ψ.hom,
        Stacks.ExtFunctorial.mapExactFunctor_comp_functor iS' vS,
        Stacks.ExtFunctorial.mapExactFunctor_comp_functor (iS' ⋙ vS) ιS,
        Ext.comp_assoc _ _ _ (zero_add q) rfl (by omega), Ext.comp_assoc _ _ _ rfl h (by omega)]
    rw [hfun]
    exact (Stacks.ExtAdjunction.precomp_mk₀_bijective_of_isIso _ _).comp
      ((bijective_mapExactFunctor_comp_stratumGysinClass i u j ι sq D γ hγ _ (eM G) (q + d₁) _
          _).comp
        ((Stacks.ExtAdjunction.extMap_bijective adjV _ _ _).comp (hδ.1 G q)))
  · have h₁ : Subsingleton (Ext (ιS.obj (vS.obj (iS'.obj G))) D q) := by
      by_cases hqc : q < c
      · exact subsingleton_ext_directImage_of_isPurityClass i u j ι sq D γ hγ _ (eM G) q hqc
      · obtain ⟨r, rfl⟩ : ∃ r, q = r + c := ⟨q - c, by omega⟩
        have := hδ.2 G r (by omega)
        have : Subsingleton (Ext (vS.obj (iS'.obj G)) (uS.obj (unitSheaf (X := T) ℓ)) r) :=
          (Stacks.ExtAdjunction.extMap_bijective adjV _ _ r).2.subsingleton
        exact (bijective_mapExactFunctor_comp_stratumGysinClass i u j ι sq D γ hγ _ (eM G) r _
          rfl).2.subsingleton
    have : Subsingleton (Ext (((iS' ⋙ vS) ⋙ ιS).obj G) D q) := h₁
    exact Function.Injective.subsingleton
      (f := fun z => (Ext.mk₀ (Ψ.inv.app G)).comp
        (Stacks.ExtAdjunction.extMap adjJ (i''S.obj G) D q z) (zero_add q))
      ((Stacks.ExtAdjunction.precomp_mk₀_bijective_of_isIso _ _).1.comp
        (Stacks.ExtAdjunction.extMap_bijective adjJ _ _ q).1)

end PointGysin

end StratumGysin

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]

/-- **The top compactly supported cohomology is free of rank one on the class of a point**
(the computation `H^{2e}_c(W) ≅ Λ` of Stacks' proof of Poincaré duality). For `W` smooth
irreducible of relative dimension `e` over `k` with a compactification `j : W → X̄`,
`H^{2e}_c(W) = Ext^{2e}_X̄(Λ, j_! Λ_W) ≅ Λ`; and for a point `i : P → N` closed in an open
`n : N → W` (`P` irreducible and étale over `k`) and a purity class `γ` of degree `2e` of `i`, the
map `z ↦ z ∘ (n ≫ j)_! γ : Ext^0_X̄(Λ, (n ≫ j)_! i_* Λ_P) → H^{2e}_c(W)` is bijective: the class
of a point generates. -/
def TopCohomologyPointClass : Prop :=
  ∀ (e : ℕ) (W : Scheme.{u}) (f : W ⟶ Spec (.of k)) [SmoothOfRelativeDimension e f]
    [TopologicalSpace.NoetherianSpace W] [IrreducibleSpace W]
    (jc : CompactificationOf (Over.mk f)),
    Nonempty (Ext (unitSheaf (X := jc.space) ℓ)
        ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj (unitSheaf (X := W) ℓ))
        (2 * e) ≃+ ZMod ℓ) ∧
    ∀ (N P : Scheme.{u}) (n : N ⟶ W) [IsOpenImmersion n] (i : P ⟶ N) [IsClosedImmersion i]
      [IrreducibleSpace P] [SmoothOfRelativeDimension 0 (i ≫ n ≫ f)]
      (γ : Ext ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj (unitSheaf (X := P) ℓ))
        ((etaleModuleRestriction.{u, 0} (ZMod ℓ) (n ≫ jc.immersion)).obj
          ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj
            (unitSheaf (X := W) ℓ))) (2 * e)),
      IsPurityClass i _ γ →
        Function.Bijective (fun z : Ext (unitSheaf (X := jc.space) ℓ)
            ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) (n ≫ jc.immersion)).obj
              ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj (unitSheaf (X := P) ℓ))) 0 =>
          z.comp (Stacks.ExtAdjunction.extMap (etaleModuleExtensionByZeroAdj.{u, 0} (ZMod ℓ)
            (n ≫ jc.immersion)) _ _ (2 * e) γ) (zero_add _))

/-- A scheme smooth and proper over `k` is noetherian. -/
private theorem isNoetherian_of_isProper_smooth {T : Scheme.{u}} (g : T ⟶ Spec (.of k))
    [IsProper g] (d : ℕ) [SmoothOfRelativeDimension d g] : IsNoetherian T := by
  have : Smooth g := SmoothOfRelativeDimension.smooth d g
  have : CompactSpace T := ⟨by
    simpa using QuasiCompact.isCompact_preimage (f := g) Set.univ isOpen_univ isCompact_univ⟩
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian g
  have : IsNoetherian T := ⟨⟩
  infer_instance

section Good

attribute [local instance] isClosedImmersion_restrictOpen_closedSpaceι
  preservesFiniteColimits_restrictOpen_closedSpaceι

variable {ℓ k} [IsAlgClosed k]

omit [IsAlgClosed k] in
/-- **The trace induced on a smooth irreducible stratum by an injective trace is injective**,
given `TopCohomologyPointClass` and a purity class `δ` of a `k`-point `i' : P → N'` of `T`,
closed in an open `a : N' → T`. -/
theorem injective_stratumTrace_of_isPurityClass (hD1 : TopCohomologyPointClass ℓ k)
    {e : ℕ} {W : Scheme.{u}} (f : W ⟶ Spec (.of k)) [SmoothOfRelativeDimension e f]
    [TopologicalSpace.NoetherianSpace W] [IrreducibleSpace W]
    (jc : CompactificationOf (Over.mk f))
    (t : Ext (unitSheaf (X := jc.space) ℓ)
      ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj (unitSheaf (X := W) ℓ))
        (2 * e) →+ ZMod ℓ) (ht : Function.Injective t)
    {N T : Scheme.{u}} (n : N ⟶ W) [IsOpenImmersion n] (i : T ⟶ N) [IsClosedImmersion i]
    [IrreducibleSpace T] (e' c : ℕ) (hc : e' + c = e) [QuasiCompact (n ≫ f)]
    [SmoothOfRelativeDimension e' (i ≫ n ≫ f)]
    (γ : Ext ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj (unitSheaf (X := T) ℓ))
      ((etaleModuleRestriction.{u, 0} (ZMod ℓ) (n ≫ jc.immersion)).obj
        ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj
          (unitSheaf (X := W) ℓ))) (2 * c))
    (hγ : IsPurityClass i _ γ) {N' P : Scheme.{u}} (a : N' ⟶ T) [IsOpenImmersion a]
    (i' : P ⟶ N') [IsClosedImmersion i'] [IsClosedImmersion (i' ≫ a)]
    [IsClosedImmersion (i' ≫ a ≫ i)] [IrreducibleSpace P]
    [SmoothOfRelativeDimension 0 (i' ≫ a ≫ (i ≫ n ≫ f))]
    [SmoothOfRelativeDimension 0 ((i' ≫ a ≫ i) ≫ n ≫ f)]
    (δ : Ext ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i').obj (unitSheaf (X := P) ℓ))
      ((etaleModuleRestriction.{u, 0} (ZMod ℓ)
          (a ≫ ((jc.restrictOpen n).closedImmersion i).toImage)).obj
        ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ)
          ((jc.restrictOpen n).closedImmersion i).toImage).obj (unitSheaf (X := T) ℓ))) (2 * e'))
    (hδ : IsPurityClass i' _ δ) :
    Function.Injective (stratumTrace i ((jc.restrictOpen n).closedImmersion i).toImage
      (n ≫ jc.immersion) ((jc.restrictOpen n).closedSpaceι i)
      ((jc.restrictOpen n).isPullback_restrictClosed i)
      ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj (unitSheaf (X := W) ℓ))
      (show 2 * e' + 2 * c = 2 * e by omega) γ t) := by
  have : TopologicalSpace.NoetherianSpace T := (i ≫ n).isEmbedding.isInducing.noetherianSpace
  let u := ((jc.restrictOpen n).closedImmersion i).toImage
  let ι : (jc.restrictOpen n).closedSpace i ⟶ jc.space := (jc.restrictOpen n).closedSpaceι i
  let sq : IsPullback i u (n ≫ jc.immersion) ι := (jc.restrictOpen n).isPullback_restrictClosed i
  let D := (etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj (unitSheaf (X := W) ℓ)
  let uS := etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) u
  let ιS := etaleModuleDirectImage.{u, 0} (ZMod ℓ) ι
  let adjJ := etaleModuleExtensionByZeroAdj.{u, 0} (ZMod ℓ) (n ≫ jc.immersion)
  let adjV := etaleModuleExtensionByZeroAdj.{u, 0} (ZMod ℓ) (a ≫ u)
  let Ψ := pointStratumDirectImageIso (ℓ := ℓ) i u (n ≫ jc.immersion) ι sq a i'
  have hN : 2 * e' + 2 * c = 2 * e := by omega
  let y := Stacks.ExtAdjunction.extMap adjV
    ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i').obj (unitSheaf (X := P) ℓ))
    (uS.obj (unitSheaf (X := T) ℓ)) (2 * e') δ
  let Θ := (y.mapExactFunctor ιS).comp (stratumGysinClass i u (n ≫ jc.immersion) ι sq D γ) hN
  obtain ⟨ε, hε⟩ := (Stacks.ExtAdjunction.extMap_bijective adjJ
    ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) (i' ≫ a ≫ i)).obj (unitSheaf (X := P) ℓ)) D
      (2 * e)).2 ((Ext.mk₀ (Ψ.hom.app (unitSheaf (X := P) ℓ))).comp Θ (zero_add _))
  have hεpur := isPurityClass_of_extMap_eq_stratumGysinClass i u (n ≫ jc.immersion) ι sq D γ
    a i' hN hγ δ hδ ε hε
  have hT := (hD1 e' T (i ≫ n ≫ f) ((jc.restrictOpen n).restrictClosed i)).2 N' P a i' δ hδ
  have hW := (hD1 e W f jc).2 N P n (i' ≫ a ≫ i) ε hεpur
  let adjι := etaleModuleInverseImageAdj.{u, 0} (ZMod ℓ) ι
  have := etaleModuleInverseImage_preservesFiniteLimits.{u, 0} (ZMod ℓ) ι
  have := etaleModuleInverseImage_preservesFiniteColimits.{u, 0} (ZMod ℓ) ι
  let M := (etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) (a ≫ u)).obj
    ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i').obj (unitSheaf (X := P) ℓ))
  let eO := unitSheafInverseImageIsoOfClosed (ℓ := ℓ) ι
  have key : ∀ x : Ext (unitSheaf (X := jc.space) ℓ) (ιS.obj M) 0,
      stratumTrace i u (n ≫ jc.immersion) ι sq D hN γ t
        (((Ext.mk₀ eO.inv).comp (Stacks.ExtAdjunction.extMap adjι _ M 0 x) (zero_add 0)).comp
          y (zero_add _)) = t (x.comp Θ (zero_add _)) := by
    intro x
    have h := Ext.transportTrace_comp (Ext.gysinTrace adjι (unitSheaf (X := jc.space) ℓ)
      (uS.obj (unitSheaf (X := T) ℓ)) D hN (stratumGysinClass i u (n ≫ jc.immersion) ι sq D γ)
        t) eO (Iso.refl _) M (zero_add (2 * e')) (Stacks.ExtAdjunction.extMap adjι _ M 0 x) y
    rw [Iso.refl_hom, Ext.comp_mk₀_id] at h
    rw [show stratumTrace i u (n ≫ jc.immersion) ι sq D hN γ t = Ext.transportTrace
      (Ext.gysinTrace adjι (unitSheaf (X := jc.space) ℓ) (uS.obj (unitSheaf (X := T) ℓ)) D hN
        (stratumGysinClass i u (n ≫ jc.immersion) ι sq D γ) t) eO (Iso.refl _) from rfl,
      h, Ext.gysinTrace_comp_extMap,
      ← Ext.comp_assoc x _ _ (zero_add _) rfl (by omega),
      ← Ext.comp_assoc x _ _ (zero_add _) hN (by omega)]
  have hA : Function.Bijective (fun x : Ext (unitSheaf (X := jc.space) ℓ) (ιS.obj M) 0 =>
      (Ext.mk₀ eO.inv).comp (Stacks.ExtAdjunction.extMap adjι _ M 0 x) (zero_add 0)) :=
    (Stacks.ExtAdjunction.precomp_mk₀_bijective_of_isIso _ _).comp
      (Stacks.ExtAdjunction.extMap_bijective adjι _ M 0)
  have hΘ : ∀ x : Ext (unitSheaf (X := jc.space) ℓ) (ιS.obj M) 0, x.comp Θ (zero_add _) =
      (x.comp (Ext.mk₀ (Ψ.inv.app (unitSheaf (X := P) ℓ))) (add_zero 0)).comp
        (Stacks.ExtAdjunction.extMap adjJ _ D (2 * e) ε) (zero_add _) := by
    intro x
    rw [hε, Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀_assoc, Iso.inv_hom_id_app]
    congr 1
    exact (Ext.mk₀_id_comp Θ).symm
  intro z₁ z₂ hz
  obtain ⟨w₁, rfl⟩ := hT.2 z₁
  obtain ⟨w₂, rfl⟩ := hT.2 z₂
  obtain ⟨x₁, rfl⟩ := hA.2 w₁
  obtain ⟨x₂, rfl⟩ := hA.2 w₂
  have hz' := ht ((key x₁).symm.trans (hz.trans (key x₂)))
  rw [hΘ, hΘ] at hz'
  have hx := (Stacks.ExtAdjunction.postcomp_mk₀_bijective_of_isIso
    (Ψ.inv.app (unitSheaf (X := P) ℓ)) 0).1 (hW.1 hz')
  rw [hx]

/-- The `k`-points of a scheme `T` locally of finite type over `k` are closed immersions. -/
theorem isClosedImmersion_pointOfClosedPoint {T : Scheme.{u}} (g : T ⟶ Spec (.of k))
    [LocallyOfFiniteType g] (x : T) (hx : IsClosed {x}) :
    IsClosedImmersion (pointOfClosedPoint (K := k) g x hx) := by
  have : IsClosedImmersion (T.fromSpecResidueField x) :=
    isClosed_singleton_iff_isClosedImmersion.mp hx
  change IsClosedImmersion
    (Spec.map (residueFieldIsoBase (K := k) g x hx).hom ≫ T.fromSpecResidueField x)
  infer_instance

/-- **The trace induced on a smooth irreducible stratum by an injective trace is injective.** Let
`W` be smooth irreducible of relative dimension `e` over `k`, `j : W → X̄` a compactification,
`t` an injective trace on `H^{2e}_c(W)`, and `T` smooth irreducible of relative dimension `e'`,
closed in an open `n : N → W`, with a purity class `γ` of degree `2c`, `e' + c = e`. Then the
trace `stratumTrace` induced on `H^{2e'}_c(T)` is injective, given local purity and
`TopCohomologyPointClass`. -/
theorem injective_stratumTrace (hpurity : LocalPurity ℓ k) (hD1 : TopCohomologyPointClass ℓ k)
    {e : ℕ} {W : Scheme.{u}} (f : W ⟶ Spec (.of k)) [SmoothOfRelativeDimension e f]
    [TopologicalSpace.NoetherianSpace W] [IrreducibleSpace W]
    (jc : CompactificationOf (Over.mk f))
    (t : Ext (unitSheaf (X := jc.space) ℓ)
      ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj (unitSheaf (X := W) ℓ))
        (2 * e) →+ ZMod ℓ) (ht : Function.Injective t)
    {N T : Scheme.{u}} (n : N ⟶ W) [IsOpenImmersion n] (i : T ⟶ N) [IsClosedImmersion i]
    [IrreducibleSpace T] (e' c : ℕ) (hc : e' + c = e) [QuasiCompact (n ≫ f)]
    [SmoothOfRelativeDimension e' (i ≫ n ≫ f)]
    (γ : Ext ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj (unitSheaf (X := T) ℓ))
      ((etaleModuleRestriction.{u, 0} (ZMod ℓ) (n ≫ jc.immersion)).obj
        ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj
          (unitSheaf (X := W) ℓ))) (2 * c))
    (hγ : IsPurityClass i _ γ) :
    Function.Injective (stratumTrace i ((jc.restrictOpen n).closedImmersion i).toImage
      (n ≫ jc.immersion) ((jc.restrictOpen n).closedSpaceι i)
      ((jc.restrictOpen n).isPullback_restrictClosed i)
      ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj (unitSheaf (X := W) ℓ))
      (show 2 * e' + 2 * c = 2 * e by omega) γ t) := by
  have : TopologicalSpace.NoetherianSpace T := (i ≫ n).isEmbedding.isInducing.noetherianSpace
  have : Nonempty T := (‹IrreducibleSpace T›).toNonempty
  obtain ⟨x, -, hx⟩ := IsClosed.exists_closed_singleton (X := T) isClosed_univ Set.univ_nonempty
  have : Smooth (i ≫ n ≫ f) := SmoothOfRelativeDimension.smooth e' (i ≫ n ≫ f)
  have : LocallyOfFinitePresentation (i ≫ n ≫ f) :=
    instLocallyOfFinitePresentationOfSmooth (i ≫ n ≫ f)
  have : LocallyOfFiniteType (i ≫ n ≫ f) :=
    instLocallyOfFiniteTypeOfLocallyOfFinitePresentation (i ≫ n ≫ f)
  let xp := pointOfClosedPoint (K := k) (i ≫ n ≫ f) x hx
  have hxp : xp ≫ i ≫ n ≫ f = 𝟙 _ := pointOfClosedPoint_comp (K := k) (i ≫ n ≫ f) x hx
  have : IsClosedImmersion xp := isClosedImmersion_pointOfClosedPoint (i ≫ n ≫ f) x hx
  have : SmoothOfRelativeDimension (0 + e') (i ≫ n ≫ f) := by
    rw [zero_add]
    infer_instance
  have : SmoothOfRelativeDimension 0 (xp ≫ i ≫ n ≫ f) := by
    rw [hxp]
    infer_instance
  obtain ⟨N', hxN', δ₀, hδ₀⟩ :=
    hpurity T (Spec (.of k)) (i ≫ n ≫ f) xp 0 e' (IsLocalRing.closedPoint k)
  have hsub : ∀ a b : Spec (.of k), a = b := fun a b =>
    PrimeSpectrum.ext ((@Ideal.eq_bot_of_prime k _ a.asIdeal a.isPrime).trans
      (@Ideal.eq_bot_of_prime k _ b.asIdeal b.isPrime).symm)
  have hP'top : ((xp ⁻¹ᵁ N' : (Spec (.of k)).Opens) : Set (Spec (.of k))) = Set.univ :=
    Set.eq_univ_of_forall fun a => by
      rw [hsub a (IsLocalRing.closedPoint k)]
      exact hxN'
  have : IsClosedImmersion (xp ⁻¹ᵁ N').ι := IsClosedImmersion.of_isPreimmersion _
    (by rw [Scheme.Opens.range_ι, hP'top]; exact isClosed_univ)
  have hi'ι : (xp ∣_ N') ≫ N'.ι = (xp ⁻¹ᵁ N').ι ≫ xp := morphismRestrict_ι xp N'
  have : IsClosedImmersion ((xp ∣_ N') ≫ N'.ι) := by
    rw [hi'ι]
    infer_instance
  have : IsClosedImmersion ((xp ∣_ N') ≫ N'.ι ≫ i) := by
    rw [← Category.assoc]
    infer_instance
  have : IrreducibleSpace (xp ⁻¹ᵁ N').toScheme := Subtype.irreducibleSpace
    ⟨⟨IsLocalRing.closedPoint k, hxN'⟩,
      Set.Subsingleton.isPreirreducible (fun a _ b _ => hsub a b)⟩
  have hP'sm : (xp ∣_ N') ≫ N'.ι ≫ (i ≫ n ≫ f) = (xp ⁻¹ᵁ N').ι := by
    rw [← Category.assoc, hi'ι, Category.assoc, hxp, Category.comp_id]
  have : SmoothOfRelativeDimension 0 ((xp ∣_ N') ≫ N'.ι ≫ (i ≫ n ≫ f)) := by
    rw [hP'sm]
    infer_instance
  have : SmoothOfRelativeDimension 0 (((xp ∣_ N') ≫ N'.ι ≫ i) ≫ n ≫ f) := by
    have h : ((xp ∣_ N') ≫ N'.ι ≫ i) ≫ n ≫ f = (xp ∣_ N') ≫ N'.ι ≫ (i ≫ n ≫ f) := by
      simp only [Category.assoc]
    rw [h, hP'sm]
    infer_instance
  exact injective_stratumTrace_of_isPurityClass hD1 f jc t ht n i e' c hc γ hγ N'.ι (xp ∣_ N')
    _ (hδ₀.comp_mk₀ (unitSheafIsoRestrictionExtensionByZero (ℓ := ℓ) N'.ι
      ((jc.restrictOpen n).closedImmersion i).toImage))

/-- **Every injective trace is good**, with any fuel `m`, for `ℓ` invertible in `k`, given
`TopCohomologyPointClass`. -/
theorem isGoodTraceAux_of_injective (hℓ : IsUnit (ℓ : k))
    (hD1 : TopCohomologyPointClass ℓ k) :
    ∀ (m e : ℕ) (W : Scheme.{u}) (f : W ⟶ Spec (.of k)) [SmoothOfRelativeDimension e f]
      [TopologicalSpace.NoetherianSpace W] [IrreducibleSpace W]
      (jc : CompactificationOf (Over.mk f))
      (t : Ext (unitSheaf (X := jc.space) ℓ)
        ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj (unitSheaf (X := W) ℓ))
          (2 * e) →+ ZMod ℓ), Function.Injective t → IsGoodTraceAux ℓ k m e f jc t := by
  intro m
  induction m with
  | zero =>
    intro e W f _ _ _ jc t ht
    exact ht
  | succ m ih =>
    intro e W f _ _ _ jc t ht
    refine ⟨ht, fun N T n _ i _ _ e' c hc _ _ _ γ hγ => ?_⟩
    have : TopologicalSpace.NoetherianSpace T := (i ≫ n).isEmbedding.isInducing.noetherianSpace
    exact ih e' T (i ≫ n ≫ f) ((jc.restrictOpen n).restrictClosed i) _
      (injective_stratumTrace (Purity.localPurity (k := k) (ℓ := ℓ) hℓ) hD1 f jc t ht n i e' c hc
        γ hγ)

/-- The transport of an injective trace on `H^{2d}(T, Λ) = Ext^{2d}(Λ_T, Λ_T)` to
`Ext^{2d}(Λ_T, 𝟙_! Λ_T)` is injective. -/
theorem injective_transportTrace_unitSheafIsoExtensionByZeroId {T : Scheme.{u}} {d : ℕ}
    (t' : Ext (unitSheaf (X := T) ℓ) (unitSheaf ℓ) (2 * d) →+ ZMod ℓ)
    (ht' : Function.Injective t') :
    Function.Injective
      (Ext.transportTrace t' (Iso.refl _) (unitSheafIsoExtensionByZeroId ℓ T)) := by
  intro z₁ z₂ h
  have h' : (Ext.mk₀ (Iso.refl (unitSheaf (X := T) ℓ)).hom).comp
      (z₁.comp (Ext.mk₀ (unitSheafIsoExtensionByZeroId ℓ T).inv) (add_zero _)) (zero_add _) =
      (Ext.mk₀ (Iso.refl (unitSheaf (X := T) ℓ)).hom).comp
        (z₂.comp (Ext.mk₀ (unitSheafIsoExtensionByZeroId ℓ T).inv) (add_zero _)) (zero_add _) :=
    ht' h
  rw [Iso.refl_hom, Ext.mk₀_id_comp, Ext.mk₀_id_comp] at h'
  exact (Stacks.ExtAdjunction.postcomp_mk₀_bijective_of_isIso
    (unitSheafIsoExtensionByZeroId ℓ T).inv (2 * d)).1 h'

/-- **Every injective trace on the top cohomology of a smooth proper irreducible variety is
good**, for its compactification by itself. Let `T` be irreducible, smooth of relative
dimension `d` and proper over the algebraically closed field `k`, and `t'` an injective trace on
`H^{2d}(T, Λ)`, with `ℓ` invertible in `k`. Given the computation of the top compactly supported
cohomology (`TopCohomologyPointClass`), the corresponding trace on `Ext^{2d}(Λ_T, 𝟙_! Λ_T)` is
good. -/
theorem isGoodTrace_of_injective (hℓ : IsUnit (ℓ : k)) (hD1 : TopCohomologyPointClass ℓ k)
    {T : Scheme.{u}} (g : T ⟶ Spec (.of k)) [IsProper g] (d : ℕ)
    [SmoothOfRelativeDimension d g] [IrreducibleSpace T]
    (t' : Ext (unitSheaf (X := T) ℓ) (unitSheaf ℓ) (2 * d) →+ ZMod ℓ)
    (ht' : Function.Injective t') :
    IsGoodTrace ℓ k d g (CompactificationOf.ofProper g)
      (Ext.transportTrace t' (Iso.refl _) (unitSheafIsoExtensionByZeroId ℓ T)) := by
  have := isNoetherian_of_isProper_smooth k g d
  exact isGoodTraceAux_of_injective hℓ hD1 d d T g (CompactificationOf.ofProper g) _
    (injective_transportTrace_unitSheafIsoExtensionByZeroId t' ht')

/-- **A good trace exists on the top cohomology of a smooth proper irreducible variety**: given
`TopCohomologyPointClass` and `ℓ` invertible in `k`, some injective trace `t'` on `H^{2d}(T, Λ)`
gives a good trace on `Ext^{2d}(Λ_T, 𝟙_! Λ_T)`. -/
theorem exists_injective_isGoodTrace (hℓ : IsUnit (ℓ : k))
    (hD1 : TopCohomologyPointClass ℓ k) {T : Scheme.{u}} (g : T ⟶ Spec (.of k)) [IsProper g]
    (d : ℕ) [SmoothOfRelativeDimension d g] [IrreducibleSpace T] :
    ∃ t' : Ext (unitSheaf (X := T) ℓ) (unitSheaf ℓ) (2 * d) →+ ZMod ℓ, Function.Injective t' ∧
      IsGoodTrace ℓ k d g (CompactificationOf.ofProper g)
        (Ext.transportTrace t' (Iso.refl _) (unitSheafIsoExtensionByZeroId ℓ T)) := by
  have := isNoetherian_of_isProper_smooth k g d
  obtain ⟨⟨φ⟩, -⟩ := hD1 d T g (CompactificationOf.ofProper g)
  let t' : Ext (unitSheaf (X := T) ℓ) (unitSheaf ℓ) (2 * d) →+ ZMod ℓ :=
    φ.toAddMonoidHom.comp ((Ext.mk₀ (unitSheafIsoExtensionByZeroId ℓ T).hom).postcomp _
      (add_zero _))
  have ht' : Function.Injective t' := fun a b hab =>
    (Stacks.ExtAdjunction.postcomp_mk₀_bijective_of_isIso
      (unitSheafIsoExtensionByZeroId ℓ T).hom (2 * d)).1 (φ.injective hab)
  exact ⟨t', ht', isGoodTrace_of_injective hℓ hD1 g d t' ht'⟩

end Good

end Stacks.EtaleCohomology
