module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingModuleGluing0BVG

/-!
# The relative dualizing module of a locally quasi-finite morphism

Let `f : Y ⟶ X` be locally of finite type and locally quasi-finite between locally Noetherian
schemes.  `StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingModuleGluing0BVG` assembles
the glueing datum of the chart sheaves of the *adapted opens* of `f`
(`Stacks.Discriminant.AdaptedOpen`) and reduces the whole existence statement of Tag 0BVG to one
hypothesis, `Stacks.Discriminant.HubRestrict`: that the two-step comparison of a chart with the
dualizing module of an adapted open commutes with restriction to a smaller adapted open, through
a map of the two algebraic relative dualizing modules that does not depend on the chart.  This
file discharges that hypothesis and so makes the glueing unconditional.

The hypothesis is proved in the two halves a nesting of adapted opens factors into, through the
intermediate adapted open with the smaller source open and the larger base open.

* With the base open fixed and the source open shrinking, the map of dualizing modules is the
  normalised localization map of Tag 0BT2 part (2) at an element presenting the smaller source
  open inside the larger.  That it intertwines the hubs is the transitivity of part (2) in the
  target ring (`Stacks.Discriminant.localizedModule_dualizingModule_equiv_trans`) followed by the
  commutation of part (2) with part (1)
  (`Stacks.Discriminant.localizedModule_dualizingModule_equiv_comm_base`); that it does not depend
  on the chart is the uniqueness of the normalised localization map
  (`Stacks.Discriminant.localizedDualizingModuleMap_eq_of_eq_id`).
* With the source open fixed and the base open shrinking, the map of dualizing modules is the
  base-replacement isomorphism of Tag 0BT2 part (1) at an element presenting the smaller base open
  inside the larger, and the whole statement is the transitivity of part (1) in the base ring
  (`Stacks.Discriminant.dualizingModule_equiv_of_isLocalization_away_trans`).

## Main definitions

* `Stacks.Discriminant.relativeDualizingModuleData`: the relative dualizing module `ω_{Y/X}`,
  with its identifications over the affine charts, as a
  `Stacks.Discriminant.RelativeDualizingModuleData`.

## Main results

* `Stacks.Discriminant.hubRestrict_of_base_eq` and
  `Stacks.Discriminant.hubRestrict_of_source_eq`: the two halves above, with the intertwining
  maps made explicit at a presenting function in
  `Stacks.Discriminant.hubRestrict_of_base_eq_of_basicOpen` and
  `Stacks.Discriminant.hubRestrict_of_source_eq_of_basicOpen`.
* `Stacks.Discriminant.hubRestrict`: `Stacks.Discriminant.HubRestrict f` holds.
* `Stacks.Discriminant.exists_relativeDualizingModule`: **Tag 0BVG, existence.** There is a
  coherent quasi-coherent `𝒪_Y`-module whose sections over every affine chart of `f` are the
  algebraic relative dualizing module of that chart, compatibly with restriction inside a chart
  and with the chart comparison over the adapted opens.
* `Stacks.Discriminant.nonempty_relativeDualizingModuleData`: **Tag 0BVG, existence, with the
  chart identifications.** That module carries the data of a
  `Stacks.Discriminant.RelativeDualizingModuleData`: identifications indexed by an affine chart
  and a finite-open factorization, independent of the factorization and compatible with shrinking
  either chart to a principal open.

## Implementation notes

Two adapted opens that share their source open, or share their base open, also share the
*presentations* of the shared open as a principal open of a given chart: goodness for a chart
asserts the existence of a presenting function, and the two existence statements are then the
same proposition, so the functions chosen from them by `Exists.choose` are equal by proof
irrelevance.  This is why both halves are stated for an adapted open built from the components of
another one — `⟨k.source, Bs, _⟩` and `⟨Ws, k.base, _⟩` — rather than for an arbitrary adapted
open with an equality hypothesis: with the shared component syntactically shared, the comparisons
the two hubs are built from are literally the same term and only the differing step has to be
compared.

For the same reason the hub comparisons are unfolded by `rfl` here rather than rewritten: the
chart hub is a `.trans` of the two steps by definition, and the proofs below state the two steps
explicitly and let definitional unfolding do the matching.

The chart-independent map of dualizing modules a nesting gives rise to can only be built from a
presentation of the smaller open as a principal open of the larger, and such a presentation
exists only once *some* chart is good for both adapted opens.  Both halves therefore split on
whether such a chart exists; where none does, the statement to be proved is vacuous and the map
is arbitrary.

## References

* [Stacks Project, Tag 0BSZ](https://stacks.math.columbia.edu/tag/0BSZ)
* [Stacks Project, Tag 0BT1](https://stacks.math.columbia.edu/tag/0BT1)
* [Stacks Project, Tag 0BT2](https://stacks.math.columbia.edu/tag/0BT2)
* [Stacks Project, Tag 0BVG](https://stacks.math.columbia.edu/tag/0BVG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry
open Stacks.AlgebraicGeometry.QuasicoherentBaseChange

universe u

namespace Stacks.Discriminant

/-- Restriction of functions along two nested inclusions of opens is a tower of algebras. -/
private theorem isScalarTower_algebraOfLE {Z : Scheme.{u}} {U V W : Z.Opens}
    (h₁ : W ≤ V) (h₂ : V ≤ U) :
    letI := algebraOfLE Z (h₁.trans h₂)
    letI := algebraOfLE Z h₂
    letI := algebraOfLE Z h₁
    IsScalarTower Γ(Z, U) Γ(Z, V) Γ(Z, W) := by
  let := algebraOfLE Z (h₁.trans h₂)
  let := algebraOfLE Z h₂
  let := algebraOfLE Z h₁
  refine IsScalarTower.of_algebraMap_eq' ?_
  change (Z.presheaf.map (homOfLE (h₁.trans h₂)).op).hom =
    ((Z.presheaf.map (homOfLE h₁).op).hom).comp (Z.presheaf.map (homOfLE h₂).op).hom
  rw [← CommRingCat.hom_comp, ← Z.presheaf.map_comp]
  congr 1

/-- Restricting a function through an intermediate open is restricting it directly. -/
private theorem presheaf_map_map {Z : Scheme.{u}} {U V W : Z.Opens} (h₁ : W ≤ V) (h₂ : V ≤ U)
    (r : Γ(Z, U)) :
    Z.presheaf.map (homOfLE h₁).op (Z.presheaf.map (homOfLE h₂).op r) =
      Z.presheaf.map (homOfLE (h₁.trans h₂)).op r := by
  rw [← ConcreteCategory.comp_apply, ← Z.presheaf.map_comp]
  congr 1

/-- The sections of a sheaf of modules over an open are a tower of modules over the rings of
functions on two larger opens. -/
private theorem isScalarTower_moduleOfLE {Z : Scheme.{u}} (M : Z.Modules) {U V W : Z.Opens}
    (h₁ : W ≤ V) (h₂ : V ≤ U) :
    letI := algebraOfLE Z h₂
    letI := moduleOfLE M (h₁.trans h₂)
    letI := moduleOfLE M h₁
    IsScalarTower Γ(Z, U) Γ(Z, V) Γ(M, W) := by
  let := algebraOfLE Z h₂
  let := moduleOfLE M (h₁.trans h₂)
  let := moduleOfLE M h₁
  refine IsScalarTower.of_algebraMap_smul fun r x ↦ ?_
  change Z.presheaf.map (homOfLE h₁).op (Z.presheaf.map (homOfLE h₂).op r) • x =
    Z.presheaf.map (homOfLE (h₁.trans h₂)).op r • x
  rw [presheaf_map_map]

/-- A localization map of modules only depends on the localization of the ring it inverts, not on
the multiplicative set presenting it. -/
private theorem isLocalizedModule_of_isLocalization {R : Type*} [CommRing R]
    (S S' : Submonoid R) (A : Type*) [CommRing A] [Algebra R A]
    [IsLocalization S A] [IsLocalization S' A]
    {N : Type*} [AddCommGroup N] [Module R N]
    {M : Type*} [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
    (g : N →ₗ[R] M) (h : IsLocalizedModule S g) : IsLocalizedModule S' g :=
  (isLocalizedModule_iff_isBaseChange S' A g).mpr
    ((isLocalizedModule_iff_isBaseChange S A g).mp h)

/-- A localization map of algebraic relative dualizing modules obtained by composing an arbitrary
one with the comparison it induces is normalised. -/
private theorem localizedModule_dualizingModule_equiv_comp_eq_id
    {A B Bg M : Type u} [CommRing A] [CommRing B] [CommRing Bg]
    [Algebra A B] [Algebra A Bg] [Algebra B Bg] [IsScalarTower A B Bg]
    [IsNoetherianRing A] [IsNoetherianRing B] [Algebra.QuasiFinite A B]
    (g : B) [IsLocalization.Away g Bg]
    (F : FiniteOpenFactorization.{u, u, u} A B)
    (G : FiniteOpenFactorization.{u, u, u} A Bg)
    [AddCommGroup M] [Module B M] [Module Bg M] [IsScalarTower B Bg M]
    [Module B (dualizingModule G)] [IsScalarTower B Bg (dualizingModule G)]
    (r₀ : dualizingModule F →ₗ[B] M) (hr₀ : IsLocalizedModule (Submonoid.powers g) r₀)
    (ρ : dualizingModule F →ₗ[B] dualizingModule G)
    (hρ : IsLocalizedModule (Submonoid.powers g) ρ)
    (hρdef : ∀ x, ρ x = localizedModule_dualizingModule_equiv g F G r₀ hr₀ (r₀ x))
    (m : dualizingModule G) :
    localizedModule_dualizingModule_equiv g F G ρ hρ m = m := by
  let e : M ≃ₗ[Bg] dualizingModule G := localizedModule_dualizingModule_equiv g F G r₀ hr₀
  obtain ⟨n, rfl⟩ := e.surjective m
  have hcomp : ∀ x : dualizingModule F,
      e.toLinearMap (r₀ x) = ρ (dualizingModuleEquiv F F x) := by
    intro x
    rw [dualizingModuleEquiv_refl]
    exact (hρdef x).symm
  have hnat := localizedModule_dualizingModule_equiv_natural_in_source
    g F F G G r₀ hr₀ ρ hρ e.toLinearMap hcomp n
  rw [dualizingModuleEquiv_refl] at hnat
  exact hnat.symm

/-- Restricting the base open of `f.appLE` gives a tower of algebras over the functions on the
base opens. -/
private theorem isScalarTower_appLE_algebraOfLE_base {X Y : Scheme.{u}} (f : Y ⟶ X)
    {U U' : X.Opens} {V : Y.Opens} (hU : U' ≤ U) (h : V ≤ f ⁻¹ᵁ U') (h' : V ≤ f ⁻¹ᵁ U) :
    letI := (f.appLE U V h').hom.toAlgebra
    letI := (f.appLE U' V h).hom.toAlgebra
    letI := algebraOfLE X hU
    IsScalarTower Γ(X, U) Γ(X, U') Γ(Y, V) := by
  let := (f.appLE U V h').hom.toAlgebra
  let := (f.appLE U' V h).hom.toAlgebra
  let := algebraOfLE X hU
  refine IsScalarTower.of_algebraMap_eq' ?_
  change (f.appLE U V h').hom =
    ((f.appLE U' V h).hom).comp (X.presheaf.map (homOfLE hU).op).hom
  rw [← CommRingCat.hom_comp, f.map_appLE h (homOfLE hU).op]

/-- Restricting the source open of `f.appLE` gives a tower of algebras over the functions on the
base open. -/
private theorem isScalarTower_appLE_algebraOfLE_source {X Y : Scheme.{u}} (f : Y ⟶ X)
    {U : X.Opens} {V V' : Y.Opens} (hV : V' ≤ V) (h : V ≤ f ⁻¹ᵁ U) (h' : V' ≤ f ⁻¹ᵁ U) :
    letI := (f.appLE U V h).hom.toAlgebra
    letI := (f.appLE U V' h').hom.toAlgebra
    letI := algebraOfLE Y hV
    IsScalarTower Γ(X, U) Γ(Y, V) Γ(Y, V') := by
  let := (f.appLE U V h).hom.toAlgebra
  let := (f.appLE U V' h').hom.toAlgebra
  let := algebraOfLE Y hV
  refine IsScalarTower.of_algebraMap_eq' ?_
  change (f.appLE U V' h').hom =
    ((Y.presheaf.map (homOfLE hV).op).hom).comp (f.appLE U V h).hom
  rw [← CommRingCat.hom_comp, ← f.appLE_map h (homOfLE hV).op]

/-- The algebra of sections of a quasi-finite morphism over an affine chart is quasi-finite. -/
private theorem quasiFinite_appLE_of_le {X Y : Scheme.{u}} (f : Y ⟶ X) [LocallyQuasiFinite f]
    (U : X.affineOpens) (V : Y.affineOpens) (h : V.1 ≤ f ⁻¹ᵁ U.1) :
    letI := (f.appLE U V h).hom.toAlgebra
    Algebra.QuasiFinite Γ(X, U.1) Γ(Y, V.1) :=
  let := (f.appLE U V h).hom.toAlgebra
  RingHom.quasiFinite_algebraMap.mp (LocallyQuasiFinite.quasiFinite_appLE U.2 V.2 h)

variable {X Y : Scheme.{u}} (f : Y ⟶ X)
  [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
  [LocallyOfFiniteType f] [LocallyQuasiFinite f]

/-- **Shrinking the base open of an adapted open, at a presenting function.** Let `l` be the
adapted open with the source open of `k` over the principal open `D(a)` of its base open. Then
the hub comparisons of `l` and `k` with a chart good for both are intertwined by the
base-replacement map of Tag 0BT2 part (1) at `a`. -/
public theorem hubRestrict_of_source_eq_of_basicOpen (k : AdaptedOpen f) (Bs : X.affineOpens)
    (hB : Bs.1 ≤ k.base.1) (hkB : k.source.1 ≤ f ⁻¹ᵁ Bs.1) (a : Γ(X, k.base.1))
    (ha : X.basicOpen a = Bs.1) :
    letI : Algebra Γ(X, k.base.1) Γ(Y, k.source.1) :=
      (f.appLE k.base k.source k.source_le).hom.toAlgebra
    letI : Algebra Γ(X, Bs.1) Γ(Y, k.source.1) := (f.appLE Bs k.source hkB).hom.toAlgebra
    letI : Algebra Γ(X, k.base.1) Γ(X, Bs.1) := algebraOfLE X hB
    letI : IsScalarTower Γ(X, k.base.1) Γ(X, Bs.1) Γ(Y, k.source.1) :=
      IsScalarTower.of_algebraMap_eq' (by
        change (f.appLE k.base.1 k.source.1 k.source_le).hom =
          ((f.appLE Bs.1 k.source.1 hkB).hom).comp (X.presheaf.map (homOfLE hB).op).hom
        rw [← CommRingCat.hom_comp, f.map_appLE hkB (homOfLE hB).op])
    letI : IsNoetherianRing Γ(X, k.base.1) := IsLocallyNoetherian.component_noetherian k.base
    letI : IsNoetherianRing Γ(Y, k.source.1) :=
      IsLocallyNoetherian.component_noetherian k.source
    letI : Algebra.QuasiFinite Γ(X, k.base.1) Γ(Y, k.source.1) :=
      RingHom.quasiFinite_algebraMap.mp
        (LocallyQuasiFinite.quasiFinite_appLE k.base.2 k.source.2 k.source_le)
    letI : IsLocalization.Away a Γ(X, Bs.1) :=
      k.base.2.isLocalization_of_eq_basicOpen _ (homOfLE hB) ha.symm
    ∀ (i : AdaptedOpen f) (hki : k.Good i.source i.base)
      (hli : AdaptedOpen.Good (f := f) ⟨k.source, Bs, hkB⟩ i.source i.base)
      (s : Γ(adaptedChartSheaf f i, k.source.1)),
      adaptedHub f ⟨k.source, Bs, hkB⟩ i hli s =
        dualizingModule_equiv_of_isLocalization_away a (adaptedFactorization f k)
          (adaptedFactorization f ⟨k.source, Bs, hkB⟩) (adaptedHub f k i hki s) := by
  let : Algebra Γ(X, k.base.1) Γ(Y, k.source.1) :=
    (f.appLE k.base k.source k.source_le).hom.toAlgebra
  let : Algebra Γ(X, Bs.1) Γ(Y, k.source.1) := (f.appLE Bs k.source hkB).hom.toAlgebra
  let : Algebra Γ(X, k.base.1) Γ(X, Bs.1) := algebraOfLE X hB
  let : IsScalarTower Γ(X, k.base.1) Γ(X, Bs.1) Γ(Y, k.source.1) :=
    isScalarTower_appLE_algebraOfLE_base f hB hkB k.source_le
  let : IsNoetherianRing Γ(X, k.base.1) := IsLocallyNoetherian.component_noetherian k.base
  let : IsNoetherianRing Γ(X, Bs.1) := IsLocallyNoetherian.component_noetherian Bs
  let : IsNoetherianRing Γ(Y, k.source.1) :=
    IsLocallyNoetherian.component_noetherian k.source
  let : Algebra.QuasiFinite Γ(X, k.base.1) Γ(Y, k.source.1) :=
    quasiFinite_appLE_of_le f k.base k.source k.source_le
  let : IsLocalization.Away a Γ(X, Bs.1) :=
    k.base.2.isLocalization_of_eq_basicOpen _ (homOfLE hB) ha.symm
  intro i hki hli s
  let : Algebra Γ(X, i.base.1) Γ(Y, k.source.1) :=
    (f.appLE i.base.1 k.source.1 (hki.le.trans i.source_le)).hom.toAlgebra
  let : Algebra Γ(X, i.base.1) Γ(X, k.base.1) := algebraOfLE X hki.baseLE
  let : Algebra Γ(X, i.base.1) Γ(X, Bs.1) := algebraOfLE X hli.baseLE
  let : IsScalarTower Γ(X, i.base.1) Γ(X, k.base.1) Γ(Y, k.source.1) :=
    isScalarTower_appLE_algebraOfLE_base f hki.baseLE k.source_le (hki.le.trans i.source_le)
  let : IsScalarTower Γ(X, i.base.1) Γ(X, Bs.1) Γ(Y, k.source.1) :=
    isScalarTower_appLE_algebraOfLE_base f hli.baseLE hkB (hki.le.trans i.source_le)
  let : IsScalarTower Γ(X, i.base.1) Γ(X, k.base.1) Γ(X, Bs.1) :=
    isScalarTower_algebraOfLE hB hki.baseLE
  let : IsNoetherianRing Γ(X, i.base.1) := IsLocallyNoetherian.component_noetherian i.base
  let : Algebra.QuasiFinite Γ(X, i.base.1) Γ(Y, k.source.1) :=
    quasiFinite_appLE_of_le f i.base k.source (hki.le.trans i.source_le)
  let : IsLocalization.Away hki.2.choose Γ(X, k.base.1) :=
    i.base.2.isLocalization_of_eq_basicOpen _ (homOfLE hki.baseLE) hki.2.choose_spec.symm
  let : IsLocalization.Away hli.2.choose Γ(X, Bs.1) :=
    i.base.2.isLocalization_of_eq_basicOpen _ (homOfLE hli.baseLE) hli.2.choose_spec.symm
  exact (dualizingModule_equiv_of_isLocalization_away_trans hki.2.choose a hli.2.choose
    (hubMiddleFactorization f i.base i.source i.source_le k hki)
    (adaptedFactorization f k) (adaptedFactorization f ⟨k.source, Bs, hkB⟩) _).symm

/-- Shrinking the base open of an adapted open, with its source open fixed, intertwines the hub
comparisons through the base-replacement map of Tag 0BT2 part (1), independently of the chart. -/
public theorem hubRestrict_of_source_eq (k : AdaptedOpen f) (Bs : X.affineOpens)
    (hB : Bs.1 ≤ k.base.1) (hkB : k.source.1 ≤ f ⁻¹ᵁ Bs.1) :
    letI : Algebra Γ(X, k.base.1) Γ(Y, k.source.1) :=
      (f.appLE k.base k.source k.source_le).hom.toAlgebra
    letI : Algebra Γ(X, Bs.1) Γ(Y, k.source.1) := (f.appLE Bs k.source hkB).hom.toAlgebra
    ∃ Θ : dualizingModule (adaptedFactorization f k) →
        dualizingModule (adaptedFactorization f ⟨k.source, Bs, hkB⟩),
      ∀ (i : AdaptedOpen f) (hki : k.Good i.source i.base)
        (hli : AdaptedOpen.Good (f := f) ⟨k.source, Bs, hkB⟩ i.source i.base)
        (s : Γ(adaptedChartSheaf f i, k.source.1)),
        adaptedHub f ⟨k.source, Bs, hkB⟩ i hli s = Θ (adaptedHub f k i hki s) := by
  classical
  by_cases hex : ∃ i : AdaptedOpen f, k.Good i.source i.base ∧
      AdaptedOpen.Good (f := f) ⟨k.source, Bs, hkB⟩ i.source i.base
  · obtain ⟨i₀, hki₀, hli₀⟩ := hex
    obtain ⟨al, hal⟩ := hli₀.2
    have he : X.basicOpen (X.presheaf.map (homOfLE hki₀.baseLE).op al) = Bs.1 := by
      rw [Scheme.basicOpen_res, hal, inf_eq_right.mpr hB]
    exact ⟨_, hubRestrict_of_source_eq_of_basicOpen f k Bs hB hkB _ he⟩
  · exact ⟨fun _ ↦ 0, fun i hki hli _ ↦ absurd ⟨i, hki, hli⟩ hex⟩

/-- **Shrinking the source open of an adapted open, at a presenting function.** Let `l` be the
adapted open with the principal open `D(c)` of the source open of `k` over the base open of `k`.
Then the hub comparisons of `k` and `l` with a chart good for both are intertwined, through
restriction of sections, by any normalised localization map of Tag 0BT2 part (2) at `c`. -/
public theorem hubRestrict_of_base_eq_of_basicOpen (k : AdaptedOpen f) (Ws : Y.affineOpens)
    (hW : Ws.1 ≤ k.source.1) (hWk : Ws.1 ≤ f ⁻¹ᵁ k.base.1) (c : Γ(Y, k.source.1))
    (hc : Y.basicOpen c = Ws.1) :
    letI : Algebra Γ(X, k.base.1) Γ(Y, k.source.1) :=
      (f.appLE k.base k.source k.source_le).hom.toAlgebra
    letI : Algebra Γ(X, k.base.1) Γ(Y, Ws.1) := (f.appLE k.base Ws hWk).hom.toAlgebra
    letI : Algebra Γ(Y, k.source.1) Γ(Y, Ws.1) := algebraOfLE Y hW
    letI : IsScalarTower Γ(X, k.base.1) Γ(Y, k.source.1) Γ(Y, Ws.1) :=
      IsScalarTower.of_algebraMap_eq' (by
        change (f.appLE k.base.1 Ws.1 hWk).hom =
          ((Y.presheaf.map (homOfLE hW).op).hom).comp
            (f.appLE k.base.1 k.source.1 k.source_le).hom
        rw [← CommRingCat.hom_comp, ← f.appLE_map k.source_le (homOfLE hW).op])
    letI : IsNoetherianRing Γ(X, k.base.1) := IsLocallyNoetherian.component_noetherian k.base
    letI : IsNoetherianRing Γ(Y, k.source.1) :=
      IsLocallyNoetherian.component_noetherian k.source
    letI : IsNoetherianRing Γ(Y, Ws.1) := IsLocallyNoetherian.component_noetherian Ws
    letI : Algebra.QuasiFinite Γ(X, k.base.1) Γ(Y, k.source.1) :=
      RingHom.quasiFinite_algebraMap.mp
        (LocallyQuasiFinite.quasiFinite_appLE k.base.2 k.source.2 k.source_le)
    letI : Algebra.QuasiFinite Γ(X, k.base.1) Γ(Y, Ws.1) :=
      RingHom.quasiFinite_algebraMap.mp
        (LocallyQuasiFinite.quasiFinite_appLE k.base.2 Ws.2 hWk)
    letI : Module Γ(Y, k.source.1)
        (dualizingModule (adaptedFactorization f ⟨Ws, k.base, hWk⟩)) :=
      Module.compHom _ (algebraMap Γ(Y, k.source.1) Γ(Y, Ws.1))
    letI : IsScalarTower Γ(Y, k.source.1) Γ(Y, Ws.1)
        (dualizingModule (adaptedFactorization f ⟨Ws, k.base, hWk⟩)) :=
      IsScalarTower.of_compHom (R := Γ(Y, k.source.1)) (A := Γ(Y, Ws.1))
        (M := dualizingModule (adaptedFactorization f ⟨Ws, k.base, hWk⟩))
    letI : IsLocalization.Away c Γ(Y, Ws.1) :=
      k.source.2.isLocalization_of_eq_basicOpen _ (homOfLE hW) hc.symm
    ∀ (r : dualizingModule (adaptedFactorization f k) →ₗ[Γ(Y, k.source.1)]
        dualizingModule (adaptedFactorization f ⟨Ws, k.base, hWk⟩))
      (hr : IsLocalizedModule (Submonoid.powers c) r),
      (∀ m, localizedModule_dualizingModule_equiv c (adaptedFactorization f k)
        (adaptedFactorization f ⟨Ws, k.base, hWk⟩) r hr m = m) →
      ∀ (i : AdaptedOpen f) (hki : k.Good i.source i.base)
        (hli : AdaptedOpen.Good (f := f) ⟨Ws, k.base, hWk⟩ i.source i.base)
        (s : Γ(adaptedChartSheaf f i, k.source.1)),
        adaptedHub f ⟨Ws, k.base, hWk⟩ i hli
            ((adaptedChartSheaf f i).presheaf.map (homOfLE hW).op s) =
          r (adaptedHub f k i hki s) := by
  let : Algebra Γ(X, k.base.1) Γ(Y, k.source.1) :=
    (f.appLE k.base k.source k.source_le).hom.toAlgebra
  let : Algebra Γ(X, k.base.1) Γ(Y, Ws.1) := (f.appLE k.base Ws hWk).hom.toAlgebra
  let : Algebra Γ(Y, k.source.1) Γ(Y, Ws.1) := algebraOfLE Y hW
  let : IsScalarTower Γ(X, k.base.1) Γ(Y, k.source.1) Γ(Y, Ws.1) :=
    isScalarTower_appLE_algebraOfLE_source f hW k.source_le hWk
  let : IsNoetherianRing Γ(X, k.base.1) := IsLocallyNoetherian.component_noetherian k.base
  let : IsNoetherianRing Γ(Y, k.source.1) :=
    IsLocallyNoetherian.component_noetherian k.source
  let : IsNoetherianRing Γ(Y, Ws.1) := IsLocallyNoetherian.component_noetherian Ws
  let : Algebra.QuasiFinite Γ(X, k.base.1) Γ(Y, k.source.1) :=
    quasiFinite_appLE_of_le f k.base k.source k.source_le
  let : Algebra.QuasiFinite Γ(X, k.base.1) Γ(Y, Ws.1) :=
    quasiFinite_appLE_of_le f k.base Ws hWk
  let : Module Γ(Y, k.source.1)
      (dualizingModule (adaptedFactorization f ⟨Ws, k.base, hWk⟩)) :=
    Module.compHom _ (algebraMap Γ(Y, k.source.1) Γ(Y, Ws.1))
  let : IsScalarTower Γ(Y, k.source.1) Γ(Y, Ws.1)
      (dualizingModule (adaptedFactorization f ⟨Ws, k.base, hWk⟩)) :=
    IsScalarTower.of_compHom (R := Γ(Y, k.source.1)) (A := Γ(Y, Ws.1))
      (M := dualizingModule (adaptedFactorization f ⟨Ws, k.base, hWk⟩))
  let : IsLocalization.Away c Γ(Y, Ws.1) :=
    k.source.2.isLocalization_of_eq_basicOpen _ (homOfLE hW) hc.symm
  intro r hr hrnorm i hki hli s
  let : Algebra Γ(X, i.base.1) Γ(Y, i.source.1) :=
    (f.appLE i.base i.source i.source_le).hom.toAlgebra
  let : Algebra Γ(X, i.base.1) Γ(Y, k.source.1) :=
    (f.appLE i.base.1 k.source.1 (hki.le.trans i.source_le)).hom.toAlgebra
  let : Algebra Γ(X, i.base.1) Γ(Y, Ws.1) :=
    (f.appLE i.base.1 Ws.1 (hli.le.trans i.source_le)).hom.toAlgebra
  let : Algebra Γ(Y, i.source.1) Γ(Y, k.source.1) := algebraOfLE Y hki.le
  let : Algebra Γ(Y, i.source.1) Γ(Y, Ws.1) := algebraOfLE Y hli.le
  let : Algebra Γ(X, i.base.1) Γ(X, k.base.1) := algebraOfLE X hki.baseLE
  let : IsScalarTower Γ(X, i.base.1) Γ(Y, i.source.1) Γ(Y, k.source.1) :=
    isScalarTower_appLE_algebraOfLE_source f hki.le i.source_le (hki.le.trans i.source_le)
  let : IsScalarTower Γ(X, i.base.1) Γ(Y, i.source.1) Γ(Y, Ws.1) :=
    isScalarTower_appLE_algebraOfLE_source f hli.le i.source_le (hli.le.trans i.source_le)
  let : IsScalarTower Γ(X, i.base.1) Γ(Y, k.source.1) Γ(Y, Ws.1) :=
    isScalarTower_appLE_algebraOfLE_source f hW (hki.le.trans i.source_le)
      (hli.le.trans i.source_le)
  let : IsScalarTower Γ(Y, i.source.1) Γ(Y, k.source.1) Γ(Y, Ws.1) :=
    isScalarTower_algebraOfLE hW hki.le
  let : IsScalarTower Γ(X, i.base.1) Γ(X, k.base.1) Γ(Y, k.source.1) :=
    isScalarTower_appLE_algebraOfLE_base f hki.baseLE k.source_le (hki.le.trans i.source_le)
  let : IsScalarTower Γ(X, i.base.1) Γ(X, k.base.1) Γ(Y, Ws.1) :=
    isScalarTower_appLE_algebraOfLE_base f hki.baseLE hWk (hli.le.trans i.source_le)
  let : IsNoetherianRing Γ(X, i.base.1) := IsLocallyNoetherian.component_noetherian i.base
  let : IsNoetherianRing Γ(Y, i.source.1) :=
    IsLocallyNoetherian.component_noetherian i.source
  let : Algebra.QuasiFinite Γ(X, i.base.1) Γ(Y, i.source.1) :=
    quasiFinite_appLE_of_le f i.base i.source i.source_le
  let : Algebra.QuasiFinite Γ(X, i.base.1) Γ(Y, k.source.1) :=
    quasiFinite_appLE_of_le f i.base k.source (hki.le.trans i.source_le)
  let : Algebra.QuasiFinite Γ(X, i.base.1) Γ(Y, Ws.1) :=
    quasiFinite_appLE_of_le f i.base Ws (hli.le.trans i.source_le)
  let : IsLocalization.Away hki.1.choose Γ(Y, k.source.1) :=
    i.source.2.isLocalization_of_eq_basicOpen _ (homOfLE hki.le) hki.1.choose_spec.symm
  let : IsLocalization.Away hli.1.choose Γ(Y, Ws.1) :=
    i.source.2.isLocalization_of_eq_basicOpen _ (homOfLE hli.le) hli.1.choose_spec.symm
  let : IsLocalization.Away hki.2.choose Γ(X, k.base.1) :=
    i.base.2.isLocalization_of_eq_basicOpen _ (homOfLE hki.baseLE) hki.2.choose_spec.symm
  let CS := Stacks.Modules.chartSheaf i.source
    (ModuleCat.of _ (dualizingModule (adaptedFactorization f i)))
  let := moduleOfLE CS hki.le
  let := moduleOfLE CS hli.le
  let := moduleOfLE CS hW
  let := isScalarTowerOfLE CS hki.le
  let := isScalarTowerOfLE CS hli.le
  let := isScalarTowerOfLE CS hW
  let := isScalarTower_moduleOfLE CS hW hki.le
  let : IsLocalization.Away
      (algebraMap Γ(Y, i.source.1) Γ(Y, k.source.1) hli.1.choose) Γ(Y, Ws.1) :=
    k.source.2.isLocalization_of_eq_basicOpen _ (homOfLE hW) (by
      change Ws.1 = Y.basicOpen (Y.presheaf.map (homOfLE hki.le).op hli.1.choose)
      rw [Scheme.basicOpen_res, hli.1.choose_spec]
      exact (inf_eq_right.mpr hW).symm)
  let Gk := hubMiddleFactorization f i.base i.source i.source_le k hki
  let Gl := hubMiddleFactorization f i.base i.source i.source_le ⟨Ws, k.base, hWk⟩ hli
  let lmk := Stacks.Modules.chartSectionOfLE i.source
    (ModuleCat.of _ (dualizingModule (adaptedFactorization f i))) hki.le
  let lml := Stacks.Modules.chartSectionOfLE i.source
    (ModuleCat.of _ (dualizingModule (adaptedFactorization f i))) hli.le
  have hlmk : IsLocalizedModule (Submonoid.powers hki.1.choose) lmk :=
    Stacks.Modules.isLocalizedModule_chartSectionOfLE i.source _ _ hki.le
      hki.1.choose_spec.symm
  have hlml : IsLocalizedModule (Submonoid.powers hli.1.choose) lml :=
    Stacks.Modules.isLocalizedModule_chartSectionOfLE i.source _ _ hli.le
      hli.1.choose_spec.symm
  let Phi2k := localizedModule_dualizingModule_equiv hki.1.choose
    (adaptedFactorization f i) Gk lmk hlmk
  let Phi1k := dualizingModule_equiv_of_isLocalization_away hki.2.choose Gk
    (adaptedFactorization f k)
  let hubk := Phi2k.trans Phi1k
  let resl := restrictₗ CS hW
  have hresi : IsLocalizedModule
      (Submonoid.powers (algebraMap Γ(Y, i.source.1) Γ(Y, k.source.1) hli.1.choose)) resl :=
    isLocalizedModule_away_of_comp (T := Γ(Y, Ws.1)) hki.1.choose hli.1.choose lmk lml resl
      hlmk hlml
      fun _ ↦ rfl
  have hres : IsLocalizedModule (Submonoid.powers c) resl :=
    isLocalizedModule_of_isLocalization _ _ Γ(Y, Ws.1) resl hresi
  let lm' := resl ∘ₗ hubk.symm.toLinearMap
  have hlm' : IsLocalizedModule (Submonoid.powers c) lm' :=
    IsLocalizedModule.of_linearEquiv_right _ resl hubk.symm
  let lmG := lm' ∘ₗ Phi1k.toLinearMap
  have hlmG : IsLocalizedModule (Submonoid.powers c) lmG :=
    IsLocalizedModule.of_linearEquiv_right _ lm' Phi1k
  have hstep2 : ∀ n : Γ(CS, Ws.1),
      localizedModule_dualizingModule_equiv c Gk Gl lmG hlmG n =
        localizedModule_dualizingModule_equiv hli.1.choose
          (adaptedFactorization f i) Gl lml hlml n :=
    localizedModule_dualizingModule_equiv_trans hki.1.choose c hli.1.choose
      (adaptedFactorization f i) Gk Gl lmk hlmk lmG hlmG lml hlml
      (fun ω ↦ (congrArg (fun x ↦ resl x) (hubk.symm_apply_apply (lmk ω))).symm)
  have hstep3 := localizedModule_dualizingModule_equiv_comm_base hki.2.choose c Gk Gl
    (adaptedFactorization f k) (adaptedFactorization f ⟨Ws, k.base, hWk⟩) lmG hlmG lm' hlm'
    (fun _ ↦ rfl) (resl s)
  have h1 : chartHub f i.base i.source i.source_le ⟨Ws, k.base, hWk⟩ hli
        (adaptedFactorization f i) (resl s) =
      dualizingModule_equiv_of_isLocalization_away hki.2.choose Gl
        (adaptedFactorization f ⟨Ws, k.base, hWk⟩)
        (localizedModule_dualizingModule_equiv c Gk Gl lmG hlmG (resl s)) := by
    rw [hstep2 (resl s)]
    rfl
  let eB := (localizedModule_dualizingModule_equiv c (adaptedFactorization f k)
    (adaptedFactorization f ⟨Ws, k.base, hWk⟩) lm' hlm').restrictScalars Γ(Y, k.source.1)
  have hrho : IsLocalizedModule (Submonoid.powers c) (eB.toLinearMap.comp lm') :=
    IsLocalizedModule.of_linearEquiv _ lm' eB
  have hrhor : eB.toLinearMap.comp lm' = r :=
    localizedDualizingModuleMap_eq_of_eq_id c (adaptedFactorization f k)
      (adaptedFactorization f ⟨Ws, k.base, hWk⟩) (eB.toLinearMap.comp lm') r hrho hr
      (localizedModule_dualizingModule_equiv_comp_eq_id c (adaptedFactorization f k)
        (adaptedFactorization f ⟨Ws, k.base, hWk⟩) lm' hlm' (eB.toLinearMap.comp lm') hrho
        fun _ ↦ rfl)
      hrnorm
  have h3 : resl s = lm' (hubk s) :=
    (congrArg (fun x ↦ resl x) (hubk.symm_apply_apply s)).symm
  have h4 : localizedModule_dualizingModule_equiv c (adaptedFactorization f k)
      (adaptedFactorization f ⟨Ws, k.base, hWk⟩) lm' hlm' (resl s) = r (hubk s) := by
    rw [h3]
    exact LinearMap.congr_fun hrhor _
  exact h1.trans (hstep3.trans h4)

/-- Shrinking the source open of an adapted open, with its base open fixed, intertwines the hub
comparisons through the normalised localization map of Tag 0BT2 part (2), independently of the
chart. -/
public theorem hubRestrict_of_base_eq (k : AdaptedOpen f) (Ws : Y.affineOpens)
    (hW : Ws.1 ≤ k.source.1) (hWk : Ws.1 ≤ f ⁻¹ᵁ k.base.1) :
    letI : Algebra Γ(X, k.base.1) Γ(Y, k.source.1) :=
      (f.appLE k.base k.source k.source_le).hom.toAlgebra
    letI : Algebra Γ(X, k.base.1) Γ(Y, Ws.1) := (f.appLE k.base Ws hWk).hom.toAlgebra
    ∃ Θ : dualizingModule (adaptedFactorization f k) →
        dualizingModule (adaptedFactorization f ⟨Ws, k.base, hWk⟩),
      ∀ (i : AdaptedOpen f) (hki : k.Good i.source i.base)
        (hli : AdaptedOpen.Good (f := f) ⟨Ws, k.base, hWk⟩ i.source i.base)
        (s : Γ(adaptedChartSheaf f i, k.source.1)),
        adaptedHub f ⟨Ws, k.base, hWk⟩ i hli
            ((adaptedChartSheaf f i).presheaf.map (homOfLE hW).op s) =
          Θ (adaptedHub f k i hki s) := by
  classical
  let : Algebra Γ(X, k.base.1) Γ(Y, k.source.1) :=
    (f.appLE k.base k.source k.source_le).hom.toAlgebra
  let : Algebra Γ(X, k.base.1) Γ(Y, Ws.1) := (f.appLE k.base Ws hWk).hom.toAlgebra
  let : Algebra Γ(Y, k.source.1) Γ(Y, Ws.1) := algebraOfLE Y hW
  let : IsScalarTower Γ(X, k.base.1) Γ(Y, k.source.1) Γ(Y, Ws.1) :=
    isScalarTower_appLE_algebraOfLE_source f hW k.source_le hWk
  let : IsNoetherianRing Γ(X, k.base.1) := IsLocallyNoetherian.component_noetherian k.base
  let : IsNoetherianRing Γ(Y, k.source.1) :=
    IsLocallyNoetherian.component_noetherian k.source
  let : IsNoetherianRing Γ(Y, Ws.1) := IsLocallyNoetherian.component_noetherian Ws
  let : Algebra.QuasiFinite Γ(X, k.base.1) Γ(Y, k.source.1) :=
    quasiFinite_appLE_of_le f k.base k.source k.source_le
  let : Algebra.QuasiFinite Γ(X, k.base.1) Γ(Y, Ws.1) :=
    quasiFinite_appLE_of_le f k.base Ws hWk
  let : Module Γ(Y, k.source.1)
      (dualizingModule (adaptedFactorization f ⟨Ws, k.base, hWk⟩)) :=
    Module.compHom _ (algebraMap Γ(Y, k.source.1) Γ(Y, Ws.1))
  let : IsScalarTower Γ(Y, k.source.1) Γ(Y, Ws.1)
      (dualizingModule (adaptedFactorization f ⟨Ws, k.base, hWk⟩)) :=
    IsScalarTower.of_compHom (R := Γ(Y, k.source.1)) (A := Γ(Y, Ws.1))
      (M := dualizingModule (adaptedFactorization f ⟨Ws, k.base, hWk⟩))
  by_cases hex : ∃ i : AdaptedOpen f, k.Good i.source i.base ∧
      AdaptedOpen.Good (f := f) ⟨Ws, k.base, hWk⟩ i.source i.base
  case neg => exact ⟨fun _ ↦ 0, fun i hki hli _ ↦ absurd ⟨i, hki, hli⟩ hex⟩
  obtain ⟨c, hc⟩ : ∃ c : Γ(Y, k.source.1), Y.basicOpen c = Ws.1 := by
    obtain ⟨i₀, hki₀, hli₀⟩ := hex
    obtain ⟨gl₀, hgl₀⟩ := hli₀.1
    exact ⟨Y.presheaf.map (homOfLE hki₀.le).op gl₀, by
      rw [Scheme.basicOpen_res, hgl₀, inf_eq_right.mpr hW]⟩
  let : IsLocalization.Away c Γ(Y, Ws.1) :=
    k.source.2.isLocalization_of_eq_basicOpen _ (homOfLE hW) hc.symm
  obtain ⟨r, hr, hrnorm⟩ := exists_localizedDualizingModuleMap_eq_id' c
    (adaptedFactorization f k) (adaptedFactorization f ⟨Ws, k.base, hWk⟩)
  exact ⟨r, hubRestrict_of_base_eq_of_basicOpen f k Ws hW hWk c hc r hr hrnorm⟩

/-- **The hub comparisons are compatible with restriction of adapted opens.** A nesting of
adapted opens factors through the adapted open with the smaller source open and the larger base
open, and the two halves are `hubRestrict_of_base_eq` and `hubRestrict_of_source_eq`. -/
public theorem hubRestrict : HubRestrict f := by
  intro k l hB hW
  obtain ⟨Θ₁, hΘ₁⟩ := hubRestrict_of_base_eq f k l.source hW (hW.trans k.source_le)
  obtain ⟨Θ₂, hΘ₂⟩ := hubRestrict_of_source_eq f
    ⟨l.source, k.base, hW.trans k.source_le⟩ l.base hB l.source_le
  refine ⟨fun m ↦ Θ₂ (Θ₁ m), fun i hki hli s ↦ ?_⟩
  have hpi : AdaptedOpen.Good (f := f) ⟨l.source, k.base, hW.trans k.source_le⟩
      i.source i.base := ⟨hli.1, hki.2⟩
  exact (hΘ₂ i hpi hli ((adaptedChartSheaf f i).presheaf.map (homOfLE hW).op s)).trans
    (congrArg Θ₂ (hΘ₁ i hki hpi s))

/-- **The relative dualizing module of a locally quasi-finite morphism of locally Noetherian
schemes exists.** There is a coherent quasi-coherent `𝒪_Y`-module whose sections over every
affine chart of `f` are the algebraic relative dualizing module of that chart, compatibly with
restriction inside a chart and with the chart comparison over the adapted opens.

This is `exists_relativeDualizingModule_of_hubRestrict` with its hypothesis discharged by
`hubRestrict`. -/
@[stacks 0BVG "existence"]
public theorem exists_relativeDualizingModule :
    ∃ (M : Y.Modules)
      (c : ∀ (i : AdaptedOpen f) (W : Y.Opens), W ≤ i.source.1 →
        Γ(M, W) ≃ₗ[Γ(Y, W)] Γ(adaptedChartSheaf f i, W)),
      M.IsQuasicoherent ∧ _root_.SheafOfModules.IsCoherent M ∧
        (∀ (i : AdaptedOpen f) (W W' : Y.Opens) (hW : W ≤ i.source.1) (h : W' ≤ W)
          (s : Γ(M, W)),
          c i W' (h.trans hW) (M.presheaf.map (homOfLE h).op s) =
            (adaptedChartSheaf f i).presheaf.map (homOfLE h).op (c i W hW s)) ∧
        (∀ (k i j : AdaptedOpen f) (hki : k.Good i.source i.base)
          (hkj : k.Good j.source j.base) (s : Γ(M, k.source.1)),
          c j k.source.1 hkj.le s =
            adaptedSheafComparison f k i j hki hkj (c i k.source.1 hki.le s)) :=
  exists_relativeDualizingModule_of_hubRestrict f (hubRestrict f)

/-! ### The relative dualizing module as chart data -/

/-- **The relative dualizing module of Tag 0BVG, as chart data.** For a morphism locally of
finite type and locally quasi-finite between locally Noetherian schemes, the module of
`Stacks.Discriminant.exists_relativeDualizingModule` carries the data of a
`Stacks.Discriminant.RelativeDualizingModuleData`: identifications of its sections over every
affine chart with the algebraic relative dualizing module of that chart, independent of the
finite-open factorization and compatible with shrinking the base chart or the source chart to a
principal open.

The identification over a chart `(U, V)` is the gluing comparison at the adapted open `(V, U)`
followed by the hub of that adapted open at itself.  The hubs of one adapted open at two charts
good for it agree on glued sections, so the two compatibilities are the explicit forms
`hubRestrict_of_source_eq_of_basicOpen` and `hubRestrict_of_base_eq_of_basicOpen` of the
restriction compatibility of the hubs. -/
@[stacks 0BVG "existence, with the chart identifications"]
public theorem nonempty_relativeDualizingModuleData : Nonempty (RelativeDualizingModuleData f) := by
  obtain ⟨M, c, hqc, hcoh, hres, hcomp⟩ := exists_relativeDualizingModule f
  have hgood : ∀ k : AdaptedOpen f, k.Good k.source k.base := fun k ↦
    ⟨⟨1, Y.basicOpen_one⟩, ⟨1, X.basicOpen_one⟩⟩
  have hindep : ∀ (k i : AdaptedOpen f) (hki : k.Good i.source i.base) (s : Γ(M, k.source.1)),
      adaptedHub f k k (hgood k) (c k k.source.1 (hgood k).le s) =
        adaptedHub f k i hki (c i k.source.1 hki.le s) := by
    intro k i hki s
    rw [hcomp k i k hki (hgood k) s]
    simp only [adaptedSheafComparison, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  let Φ : ∀ k : AdaptedOpen f,
      let : Algebra Γ(X, k.base.1) Γ(Y, k.source.1) :=
        (f.appLE k.base k.source k.source_le).hom.toAlgebra
      Γ(M, k.source.1) ≃ₗ[Γ(Y, k.source.1)] dualizingModule (adaptedFactorization f k) :=
    fun k ↦ (c k k.source.1 (hgood k).le).trans (adaptedHub f k k (hgood k))
  refine ⟨{
    sheaf := M
    isQuasicoherent := hqc
    isCoherent := hcoh
    factorization := fun U V hVU ↦ nonempty_relativeDualizingChartFactorization f U V hVU
    localEquiv := fun U V hVU F ↦
      let : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
      let : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
      (Φ ⟨V, U, hVU⟩).trans (dualizingModuleEquiv (adaptedFactorization f ⟨V, U, hVU⟩) F)
    localEquiv_natural := ?_
    localEquiv_baseBasicOpen := ?_
    localEquiv_basicOpen := ?_ }⟩
  · intro U V hVU F G s
    let : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
    let : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
    change dualizingModuleEquiv (adaptedFactorization f ⟨V, U, hVU⟩) G (Φ ⟨V, U, hVU⟩ s) =
      dualizingModuleEquiv F G
        (dualizingModuleEquiv (adaptedFactorization f ⟨V, U, hVU⟩) F (Φ ⟨V, U, hVU⟩ s))
    rw [← dualizingModuleEquiv_trans (adaptedFactorization f ⟨V, U, hVU⟩) F G]
    rfl
  · intro U V hVU a hVa Ua F G s
    let : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
    let : Algebra Γ(X, Ua.1) Γ(Y, V.1) := (f.appLE Ua V hVa).hom.toAlgebra
    let : Algebra Γ(X, U.1) Γ(X, Ua.1) :=
      (X.presheaf.map (homOfLE (X.basicOpen_le a)).op).hom.toAlgebra
    let : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
    let : IsNoetherianRing Γ(X, Ua.1) := IsLocallyNoetherian.component_noetherian Ua
    let : IsNoetherianRing Γ(Y, V.1) := IsLocallyNoetherian.component_noetherian V
    let : Algebra.QuasiFinite Γ(X, U.1) Γ(Y, V.1) := quasiFinite_appLE_of_le f U V hVU
    let : IsLocalization.Away a Γ(X, Ua.1) := U.2.isLocalization_basicOpen a
    let : IsScalarTower Γ(X, U.1) Γ(X, Ua.1) Γ(Y, V.1) :=
      isScalarTower_appLE_algebraOfLE_base f (X.basicOpen_le a) hVa hVU
    have hgoodaU : AdaptedOpen.Good (f := f) ⟨V, Ua, hVa⟩ V U :=
      ⟨⟨1, Y.basicOpen_one⟩, ⟨a, rfl⟩⟩
    have h1 := hindep ⟨V, Ua, hVa⟩ ⟨V, U, hVU⟩ hgoodaU s
    have h2 := hubRestrict_of_source_eq_of_basicOpen f ⟨V, U, hVU⟩ Ua (X.basicOpen_le a) hVa
      a rfl ⟨V, U, hVU⟩ (hgood ⟨V, U, hVU⟩) hgoodaU (c ⟨V, U, hVU⟩ V.1 (hgood ⟨V, U, hVU⟩).le s)
    have h3 := dualizingModule_equiv_of_isLocalization_away_natural a
      (adaptedFactorization f ⟨V, U, hVU⟩) (adaptedFactorization f ⟨V, U, hVU⟩)
      (adaptedFactorization f ⟨V, Ua, hVa⟩) G (Φ ⟨V, U, hVU⟩ s)
    have h4 := dualizingModule_equiv_of_isLocalization_away_natural a
      (adaptedFactorization f ⟨V, U, hVU⟩) F G G (Φ ⟨V, U, hVU⟩ s)
    rw [dualizingModuleEquiv_refl, LinearEquiv.refl_apply] at h3 h4
    exact (congrArg (dualizingModuleEquiv (adaptedFactorization f ⟨V, Ua, hVa⟩) G)
      (h1.trans h2)).trans (h3.trans h4)
  · intro U V hVU g W hWU F G
    let : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
    let : Algebra Γ(X, U.1) Γ(Y, W.1) := (f.appLE U W hWU).hom.toAlgebra
    let : Algebra Γ(Y, V.1) Γ(Y, W.1) :=
      (Y.presheaf.map (homOfLE (Y.basicOpen_le g)).op).hom.toAlgebra
    let : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
    let : IsNoetherianRing Γ(Y, V.1) := IsLocallyNoetherian.component_noetherian V
    let : Algebra.QuasiFinite Γ(X, U.1) Γ(Y, V.1) := quasiFinite_appLE_of_le f U V hVU
    let : IsLocalization.Away g Γ(Y, W.1) := V.2.isLocalization_basicOpen g
    let : IsScalarTower Γ(X, U.1) Γ(Y, V.1) Γ(Y, W.1) :=
      isScalarTower_appLE_algebraOfLE_source f (Y.basicOpen_le g) hVU hWU
    let : Module Γ(Y, V.1) (dualizingModule G) :=
      Module.compHom (dualizingModule G) (algebraMap Γ(Y, V.1) Γ(Y, W.1))
    let : IsScalarTower Γ(Y, V.1) Γ(Y, W.1) (dualizingModule G) :=
      IsScalarTower.of_compHom Γ(Y, V.1) Γ(Y, W.1) _
    let : Module Γ(Y, V.1) (dualizingModule (adaptedFactorization f ⟨W, U, hWU⟩)) :=
      Module.compHom _ (algebraMap Γ(Y, V.1) Γ(Y, W.1))
    let : IsScalarTower Γ(Y, V.1) Γ(Y, W.1)
        (dualizingModule (adaptedFactorization f ⟨W, U, hWU⟩)) :=
      IsScalarTower.of_compHom Γ(Y, V.1) Γ(Y, W.1) _
    obtain ⟨ρ, hρ, hρn⟩ := exists_localizedDualizingModuleMap_eq_id' g
      (adaptedFactorization f ⟨V, U, hVU⟩) (adaptedFactorization f ⟨W, U, hWU⟩)
    let eF := dualizingModuleEquiv (adaptedFactorization f ⟨V, U, hVU⟩) F
    let eG := dualizingModuleEquiv (adaptedFactorization f ⟨W, U, hWU⟩) G
    let r : dualizingModule F →ₗ[Γ(Y, V.1)] dualizingModule G :=
      (eG.restrictScalars Γ(Y, V.1)).toLinearMap ∘ₗ ρ ∘ₗ eF.symm.toLinearMap
    have hρ' : IsLocalizedModule (Submonoid.powers g) (ρ ∘ₗ eF.symm.toLinearMap) :=
      IsLocalizedModule.of_linearEquiv_right _ ρ eF.symm
    have hr : IsLocalizedModule (Submonoid.powers g) r :=
      IsLocalizedModule.of_linearEquiv _ (ρ ∘ₗ eF.symm.toLinearMap)
        (eG.restrictScalars Γ(Y, V.1))
    have hcmp : ∀ x, eG (ρ x) = r (eF x) := fun x ↦ by simp [r]
    refine ⟨r, hr, fun s ↦ ?_, fun m ↦ ?_⟩
    · have hgoodWV : AdaptedOpen.Good (f := f) ⟨W, U, hWU⟩ V U :=
        ⟨⟨g, rfl⟩, ⟨1, X.basicOpen_one⟩⟩
      have e1 := hindep ⟨W, U, hWU⟩ ⟨V, U, hVU⟩ hgoodWV (restrictₗ M (Y.basicOpen_le g) s)
      have e2 := hres ⟨V, U, hVU⟩ V.1 W.1 (hgood ⟨V, U, hVU⟩).le (Y.basicOpen_le g) s
      have e3 := hubRestrict_of_base_eq_of_basicOpen f ⟨V, U, hVU⟩ W (Y.basicOpen_le g) hWU g
        rfl ρ hρ hρn ⟨V, U, hVU⟩ (hgood ⟨V, U, hVU⟩) hgoodWV
        (c ⟨V, U, hVU⟩ V.1 (hgood ⟨V, U, hVU⟩).le s)
      exact (congrArg eG (e1.trans ((congrArg (adaptedHub f ⟨W, U, hWU⟩ ⟨V, U, hVU⟩ hgoodWV)
        e2).trans e3))).trans (hcmp _)
    · have hnat := localizedModule_dualizingModule_equiv_natural_in_source g
        (adaptedFactorization f ⟨V, U, hVU⟩) F (adaptedFactorization f ⟨W, U, hWU⟩) G ρ hρ r hr
        eG.toLinearMap hcmp (eG.symm m)
      rw [hρn, show eG.toLinearMap (eG.symm m) = m from eG.apply_symm_apply m] at hnat
      exact hnat.symm.trans (eG.apply_symm_apply m)

/-- **The relative dualizing module** `ω_{Y/X}` of a morphism locally of finite type and locally
quasi-finite between locally Noetherian schemes, together with its identifications
`Γ(V, ω_{Y/X}) = ω_{Γ(Y, V)/Γ(X, U)}` over the affine charts of the morphism.  By the uniqueness
half of Tag 0BVG, `Stacks.Discriminant.existsUnique_relativeDualizingComparison`, any other
module carrying such identifications is canonically isomorphic to it. -/
public noncomputable def relativeDualizingModuleData : RelativeDualizingModuleData f :=
  (nonempty_relativeDualizingModuleData f).some

end Stacks.Discriminant

end
