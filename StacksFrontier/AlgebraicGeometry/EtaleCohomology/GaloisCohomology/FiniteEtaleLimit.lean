module

public import StacksFrontier.AlgebraicGeometry.CofilteredLimits.Integral
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedPointDirectSumCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.PullbackSheafSystemPresentation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SheafSystemCohomologyColimit
public import StacksFrontier.CategoryTheory.Limits.SystemColimitLift
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.MethodeDeLa.FiniteEtaleTrace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PrimePowerTorsionPushforward

/-!
# Cohomology of limits of finite étale schemes of degree prime to `ℓ`

Let `S` be a quasi-compact and quasi-separated scheme and let `X = lim Xᵢ` be the limit of a
directed inverse system of `S`-schemes, each `ιᵢ : Xᵢ ⟶ S` finite étale of constant degree prime to
a prime `ℓ`; write `g : X ⟶ S` for the structure morphism. Then for `n > 0` there is an `ℓ`-power
torsion sheaf `G` on `S_étale` with `Hⁿ(S, G) ≠ 0` if and only if there is an `ℓ`-power torsion
sheaf `F` on `X_étale` with `Hⁿ(X, F) ≠ 0` ([Stacks, Tag 0DV7]); in fact one may take `F = g⁻¹ G`
and `G = g_* F`.

From `X` to `S`: the morphism `g` is integral, being a limit of finite morphisms
(`AlgebraicGeometry.isIntegralHom_of_isLimit`), so `g_*` is exact, preserves `ℓ`-power torsion and
does not change cohomology (`Stacks.EtaleCohomology.sheafHSmallEtalePushforwardAddEquiv`).

From `S` to `X`: the pullback `Hⁿ(S, G) ⟶ Hⁿ(Xᵢ, ιᵢ⁻¹ G)` is injective at every stage by the
méthode de la trace, and `Hⁿ(X, g⁻¹ G)` is the colimit of the `Hⁿ(Xᵢ, ιᵢ⁻¹ G)`
([Stacks, Tag 09YQ], applied to the system of inverse images of `G`), so a nonzero class stays
nonzero on `X`.

## Main results

* `Stacks.EtaleCohomology.exists_isPrimePowerTorsion_nontrivial_sheafH_iff_of_isLimit`:
  [Stacks, Tag 0DV7], the equivalence of the two nonvanishing conditions.
* `Stacks.EtaleCohomology.isPrimePowerTorsion_nontrivial_sheafH_smallEtalePullbackAb_of_isLimit`:
  the direction from `S` to `X`, with `F = g⁻¹ G`.
* The direction from `X` to `S`, with `G = g_* F`, is
  `Stacks.EtaleCohomology.isPrimePowerTorsion_nontrivial_sheafH_smallEtalePushforwardAb_of_isLimit`
* `Stacks.EtaleCohomology.injective_etaleCohomologyPullback_of_isLimit`: pulling back
  `Hⁿ(S, G) ⟶ Hⁿ(X, g⁻¹ G)` is injective for `ℓ`-power torsion `G`.
* `Stacks.EtaleCohomology.injective_etaleCohomologyPullback_of_isSystemColimit`: injectivity of
  the pullback to the limit from injectivity at the stages, when the cohomology of the limit is
  the colimit of the cohomology of the stages.

## Implementation notes

The directed system is a functor `D : Iᵒᵖ ⥤ Scheme` over a directed nonempty preorder `I`
together with compatible structure morphisms `ιᵢ : Xᵢ ⟶ S`, and the limit is a limit cone `c` with
structure morphism `g` satisfying `c.π.app i ≫ ιᵢ = g`. "Finite étale of constant degree `dᵢ`" is
`AlgebraicGeometry.IsFinite`, `AlgebraicGeometry.Etale` and
`Stacks.Morphisms.IsFiniteLocallyFreeOfRank (ιᵢ) (dᵢ)`. The hypotheses that `ℓ` is prime and
`n > 0` are not needed and are omitted. The direction from `X` to `S` only uses that the `ιᵢ` are
finite.

## References

* [Stacks Project, Tag 0DV7](https://stacks.math.columbia.edu/tag/0DV7)
* [Stacks Project, Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

/-- **Pulling back in two steps.** Pulling back along `f` and then along `a`, with the comparison
`a⁻¹ f⁻¹ ≅ (a ≫ f)⁻¹` of inverse images, is pulling back along the composite. -/
theorem etaleCohomologyPullback_comp'_hom_app {W Y Z : Scheme.{u}} (a : W ⟶ Y) (f : Y ⟶ Z)
    (af : W ⟶ Z) (h : af = a ≫ f) (F : Sheaf (smallEtaleTopology Z) Ab.{u + 1}) (q : ℕ)
    (x : Sheaf.H.{u + 1} F q) :
    etaleCohomologyPullback a ((smallEtalePullbackAbComp' a f af h).hom.app F) q
      (etaleCohomologyPullback f (𝟙 _) q x) = etaleCohomologyPullback af (𝟙 _) q x := by
  rw [etaleCohomologyPullback_comp a f af h]
  congr 2
  simp

/-- **Direct image along an integral morphism detects nonvanishing of cohomology.** -/
theorem nontrivial_sheafH_smallEtalePushforwardAb_iff {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegralHom f] (F : Sheaf (smallEtaleTopology X) Ab.{u + 1}) (q : ℕ) :
    Nontrivial (Sheaf.H.{u + 1} ((smallEtalePushforwardAb f).obj F) q) ↔
      Nontrivial (Sheaf.H.{u + 1} F q) :=
  (sheafHSmallEtalePushforwardAddEquiv f F q).toEquiv.nontrivial_congr.symm

variable {I : Type u} [Preorder I] {D : Iᵒᵖ ⥤ Scheme.{u}} {S : Scheme.{u}}
  (ι : ∀ i, D.obj i ⟶ S) (hι : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), D.map a ≫ ι j = ι i)
  (c : Cone D) (g : c.pt ⟶ S) (hg : ∀ i, c.π.app i ≫ ι i = g)

include hι hg in
/-- The structure morphism of a directed limit of schemes integral over `S` is integral. -/
theorem isIntegralHom_of_isLimit_of_isDirected [IsDirected I (· ≤ ·)] [Nonempty I]
    [∀ i, IsIntegralHom (ι i)] (hc : IsLimit c) : IsIntegralHom g := by
  obtain ⟨i⟩ := (inferInstance : Nonempty I)
  rw [← hg (op i)]
  exact isIntegralHom_of_isLimit D ι (fun _ _ a => hι a) c hc (op i)

include hι hg in
/-- **[Stacks, Tag 0DV7], from the limit to the base.** For a directed limit `X = lim Xᵢ` of
schemes finite over `S`, an `ℓ`-power torsion sheaf `F` on `X` with `Hⁿ(X, F) ≠ 0` gives the
`ℓ`-power torsion sheaf `g_* F` on `S` with `Hⁿ(S, g_* F) ≠ 0`. -/
@[stacks 0DV7 "given F on X, take G = g_* F"]
theorem isPrimePowerTorsion_nontrivial_sheafH_smallEtalePushforwardAb_of_isLimit
    [IsDirected I (· ≤ ·)] [Nonempty I] [∀ i, IsFinite (ι i)] (hc : IsLimit c) {ℓ : ℕ}
    {F : Sheaf (smallEtaleTopology c.pt) Ab.{u + 1}}
    (hF : Stacks.Torsion.IsPrimePowerTorsion (smallEtaleTopology c.pt) ℓ F) {n : ℕ}
    (hn : Nontrivial (Sheaf.H.{u + 1} F n)) :
    Stacks.Torsion.IsPrimePowerTorsion (smallEtaleTopology S) ℓ
        ((smallEtalePushforwardAb g).obj F) ∧
      Nontrivial (Sheaf.H.{u + 1} ((smallEtalePushforwardAb g).obj F) n) := by
  have := isIntegralHom_of_isLimit_of_isDirected ι hι c g hg hc
  exact ⟨isPrimePowerTorsion_smallEtalePushforwardAb g hF,
    (nontrivial_sheafH_smallEtalePushforwardAb_iff g F n).mpr hn⟩

include hι in
/-- **Pulling back to the stages along the transition maps.** For the system of inverse images
`ι_i⁻¹ G` of one sheaf, the transition map of cohomology sends the pullback of a class to `X_i`
to its pullback to `X_j`. -/
theorem etaleCohomologyPullback_ofCocone_map {i j : Iᵒᵖ} (a : i ⟶ j)
    (G : Sheaf (smallEtaleTopology S) Ab.{u + 1}) (q : ℕ) (x : Sheaf.H.{u + 1} G q) :
    etaleCohomologyPullback (D.map a) ((EtaleSheafSystem.ofCocone ι hι G).map a) q
      (etaleCohomologyPullback (ι j) (𝟙 _) q x) = etaleCohomologyPullback (ι i) (𝟙 _) q x :=
  etaleCohomologyPullback_comp'_hom_app _ _ _ (hι a).symm G q x

include hg in
/-- **Pulling back from a stage to the limit.** The pullback of the class of `x` on `X_i` along
the projection `X ⟶ X_i`, followed by the comparison `π_i⁻¹ ι_i⁻¹ G ≅ g⁻¹ G`, is the pullback of
`x` along `g`. -/
theorem etaleCohomologyPullback_π_app_etaleCohomologyPullback (i : Iᵒᵖ)
    (G : Sheaf (smallEtaleTopology S) Ab.{u + 1}) (q : ℕ) (x : Sheaf.H.{u + 1} G q) :
    etaleCohomologyPullback (c.π.app i)
        ((smallEtalePullbackAbComp' (c.π.app i) (ι i) g (hg i).symm).hom.app G) q
      (etaleCohomologyPullback (ι i) (𝟙 _) q x) = etaleCohomologyPullback g (𝟙 _) q x :=
  etaleCohomologyPullback_comp'_hom_app _ _ _ (hg i).symm G q x

include hι in
/-- **The cohomology of the system of inverse images of one sheaf is functorial**: pulling back
along `a ≫ b` is pulling back along `b` and then along `a`. -/
theorem etaleCohomologyPullback_ofCocone_map_comp {i j k : Iᵒᵖ} (a : i ⟶ j) (b : j ⟶ k)
    (G : Sheaf (smallEtaleTopology S) Ab.{u + 1}) (q : ℕ)
    (y : Sheaf.H.{u + 1} ((EtaleSheafSystem.ofCocone ι hι G).obj k) q) :
    etaleCohomologyPullback (D.map (a ≫ b)) ((EtaleSheafSystem.ofCocone ι hι G).map (a ≫ b)) q y =
      etaleCohomologyPullback (D.map a) ((EtaleSheafSystem.ofCocone ι hι G).map a) q
        (etaleCohomologyPullback (D.map b) ((EtaleSheafSystem.ofCocone ι hι G).map b) q y) := by
  rw [etaleCohomologyPullback_comp (D.map a) (D.map b) (D.map (a ≫ b)) (D.map_comp a b)]
  congr 2
  have hp := smallEtalePullbackAbComp'_assoc_app (D.map a) (D.map b) (ι k) (D.map (a ≫ b))
    (D.map_comp a b) (ι j) (hι b).symm (ι i) (hι (a ≫ b)).symm (hι a).symm G
  dsimp only [EtaleSheafSystem.ofCocone]
  rw [← cancel_epi ((smallEtalePullbackAbComp' (D.map a) (D.map b) (D.map (a ≫ b))
    (D.map_comp a b)).hom.app ((smallEtalePullbackAb (ι k)).obj G)),
    Iso.hom_inv_id_app_assoc, hp]

include hι hg in
/-- **The legs of the cohomology of the system of inverse images are compatible**: pulling back
along a transition morphism and then to the limit is pulling back to the limit directly. -/
theorem etaleCohomologyPullback_ofCoconeLeg_comp {i j : Iᵒᵖ} (a : i ⟶ j)
    (G : Sheaf (smallEtaleTopology S) Ab.{u + 1}) (q : ℕ)
    (y : Sheaf.H.{u + 1} ((EtaleSheafSystem.ofCocone ι hι G).obj j) q) :
    etaleCohomologyPullback (c.π.app i) (EtaleSheafSystem.ofCoconeLeg ι hι c g hg G i) q
        (etaleCohomologyPullback (D.map a) ((EtaleSheafSystem.ofCocone ι hι G).map a) q y) =
      etaleCohomologyPullback (c.π.app j) (EtaleSheafSystem.ofCoconeLeg ι hι c g hg G j) q y := by
  rw [etaleCohomologyPullback_comp (c.π.app i) (D.map a) (c.π.app j) (c.w a).symm]
  congr 2
  have h := EtaleSheafSystem.isPullbackCocone_ofCocone ι hι c g hg G a
  rw [conePullbackComp_eq] at h
  exact h

include hι in
/-- The transition maps of the cohomology of the system of inverse images, as morphisms of
abelian groups, compose: `etaleCohomologyPullback_ofCocone_map_comp` in `AddCommGrpCat`. -/
theorem ofHom_etaleCohomologyPullback_ofCocone_map_comp
    (G : Sheaf (smallEtaleTopology S) Ab.{u + 1}) (q : ℕ) {i j k : Iᵒᵖ} (a : i ⟶ j)
    (b : j ⟶ k) :
    AddCommGrpCat.ofHom (etaleCohomologyPullback (D.map (a ≫ b))
        ((EtaleSheafSystem.ofCocone ι hι G).map (a ≫ b)) q) =
      AddCommGrpCat.ofHom (etaleCohomologyPullback (D.map b)
        ((EtaleSheafSystem.ofCocone ι hι G).map b) q) ≫
      AddCommGrpCat.ofHom (etaleCohomologyPullback (D.map a)
        ((EtaleSheafSystem.ofCocone ι hι G).map a) q) := by
  ext y
  exact etaleCohomologyPullback_ofCocone_map_comp ι hι a b G q y

include hι hg in
/-- The legs of the cohomology of the system of inverse images, as morphisms of abelian groups,
are compatible with its transition maps: `etaleCohomologyPullback_ofCoconeLeg_comp` in
`AddCommGrpCat`. -/
theorem ofHom_etaleCohomologyPullback_ofCoconeLeg_comp
    (G : Sheaf (smallEtaleTopology S) Ab.{u + 1}) (q : ℕ) {i j : Iᵒᵖ} (a : i ⟶ j) :
    AddCommGrpCat.ofHom (etaleCohomologyPullback (D.map a)
        ((EtaleSheafSystem.ofCocone ι hι G).map a) q) ≫
      AddCommGrpCat.ofHom (etaleCohomologyPullback (c.π.app i)
        (EtaleSheafSystem.ofCoconeLeg ι hι c g hg G i) q) =
    AddCommGrpCat.ofHom (etaleCohomologyPullback (c.π.app j)
        (EtaleSheafSystem.ofCoconeLeg ι hι c g hg G j) q) := by
  ext y
  exact etaleCohomologyPullback_ofCoconeLeg_comp ι hι c g hg a G q y

include hι hg in
/-- **Injectivity on the limit from injectivity at the stages.** If the cohomology of the system of
inverse images `ι_i⁻¹ G` has the cohomology of `g⁻¹ G` as colimit and every pullback
`Hⁿ(S, G) ⟶ Hⁿ(X_i, ι_i⁻¹ G)` is injective, then so is `Hⁿ(S, G) ⟶ Hⁿ(X, g⁻¹ G)`. -/
theorem injective_etaleCohomologyPullback_of_isSystemColimit [IsDirected I (· ≤ ·)] [Nonempty I]
    (G : Sheaf (smallEtaleTopology S) Ab.{u + 1}) (q : ℕ)
    (hcoh : IsSystemColimit
      (fun i => AddCommGrpCat.of (Sheaf.H.{u + 1} ((EtaleSheafSystem.ofCocone ι hι G).obj i) q))
      (fun a => AddCommGrpCat.ofHom
        (etaleCohomologyPullback (D.map a) ((EtaleSheafSystem.ofCocone ι hι G).map a) q))
      (AddCommGrpCat.of (Sheaf.H.{u + 1} ((smallEtalePullbackAb g).obj G) q))
      (fun i => AddCommGrpCat.ofHom (etaleCohomologyPullback (c.π.app i)
        (EtaleSheafSystem.ofCoconeLeg ι hι c g hg G i) q)))
    (hinj : ∀ i, Function.Injective
      (etaleCohomologyPullback (ι i) (𝟙 ((smallEtalePullbackAb (ι i)).obj G)) q)) :
    Function.Injective (etaleCohomologyPullback g (𝟙 ((smallEtalePullbackAb g).obj G)) q) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨i₀⟩ := (inferInstance : Nonempty I)
  obtain ⟨j, a, ha⟩ := IsSystemColimit.exists_eq_zero
    (fun a b => ofHom_etaleCohomologyPullback_ofCocone_map_comp ι hι G q a b)
    (fun a => ofHom_etaleCohomologyPullback_ofCoconeLeg_comp ι hι c g hg G q a) hcoh
    (i := op i₀) (etaleCohomologyPullback (ι (op i₀)) (𝟙 _) q x)
    ((etaleCohomologyPullback_π_app_etaleCohomologyPullback ι c g hg (op i₀) G q x).trans hx)
  have ha' : etaleCohomologyPullback (D.map a) ((EtaleSheafSystem.ofCocone ι hι G).map a) q
      (etaleCohomologyPullback (ι (op i₀)) (𝟙 _) q x) = 0 := ha
  rw [etaleCohomologyPullback_ofCocone_map ι hι a G q x] at ha'
  exact (injective_iff_map_eq_zero _).mp (hinj j) x ha'

include hι hg in
/-- **[Stacks, Tag 0DV7], injectivity from the base to the limit.** Let `S` be quasi-compact and
quasi-separated and let `X = lim Xᵢ` be a directed limit of `S`-schemes `ιᵢ : Xᵢ ⟶ S`, each finite
étale of constant degree `dᵢ` prime to `ℓ`. For an `ℓ`-power torsion sheaf `G` on `S`, pulling
back `Hⁿ(S, G) ⟶ Hⁿ(X, g⁻¹ G)` is injective: it is injective at every stage by the méthode de la
trace, and `Hⁿ(X, g⁻¹ G)` is the colimit of the `Hⁿ(Xᵢ, ιᵢ⁻¹ G)` by [Stacks, Tag 09YQ]. -/
theorem injective_etaleCohomologyPullback_of_isLimit [IsDirected I (· ≤ ·)] [Nonempty I]
    [CompactSpace S] [QuasiSeparatedSpace S] [∀ i, IsFinite (ι i)] [∀ i, Etale (ι i)]
    (d : Iᵒᵖ → ℕ) [∀ i, Stacks.Morphisms.IsFiniteLocallyFreeOfRank (ι i) (d i)] {ℓ : ℕ}
    (hd : ∀ i, (d i).Coprime ℓ) (hc : IsLimit c) {G : Sheaf (smallEtaleTopology S) Ab.{u + 1}}
    (hG : Stacks.Torsion.IsPrimePowerTorsion (smallEtaleTopology S) ℓ G) (n : ℕ) :
    Function.Injective (etaleCohomologyPullback g (𝟙 ((smallEtalePullbackAb g).obj G)) n) := by
  have : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a) := fun a =>
    (isIntegralHom_map_of_isIntegralHom_comp D ι (fun _ _ a => hι a) a).toIsAffineHom
  have : ∀ i, CompactSpace (D.obj i) := fun i => QuasiCompact.compactSpace_of_compactSpace (ι i)
  have : ∀ i, QuasiSeparatedSpace (D.obj i) := fun i =>
    quasiSeparatedSpace_of_quasiSeparated (ι i)
  exact injective_etaleCohomologyPullback_of_isSystemColimit ι hι c g hg G n
    (EtaleSheafSystem.isSystemColimit_etaleCohomologyPullback hc n
      (EtaleSheafSystem.ofCocone ι hι G) _ (EtaleSheafSystem.ofCoconeLeg ι hι c g hg G)
      (EtaleSheafSystem.isPullbackCocone_ofCocone ι hι c g hg G)
      (EtaleSheafSystem.isPullbackColimitPresentation_ofCocone ι hι c g hg G))
    fun i => injective_etaleCohomologyPullback_of_isPrimePowerTorsion (ι i) G (hd i) hG n

include hι hg in
/-- **[Stacks, Tag 0DV7], from the base to the limit.** In the situation of
`Stacks.EtaleCohomology.injective_etaleCohomologyPullback_of_isLimit`, an `ℓ`-power torsion sheaf
`G` on `S` with `Hⁿ(S, G) ≠ 0` gives the `ℓ`-power torsion sheaf `g⁻¹ G` on `X` with
`Hⁿ(X, g⁻¹ G) ≠ 0`. -/
@[stacks 0DV7 "given G on S, take F = g⁻¹ G"]
theorem isPrimePowerTorsion_nontrivial_sheafH_smallEtalePullbackAb_of_isLimit
    [IsDirected I (· ≤ ·)] [Nonempty I] [CompactSpace S] [QuasiSeparatedSpace S]
    [∀ i, IsFinite (ι i)] [∀ i, Etale (ι i)] (d : Iᵒᵖ → ℕ)
    [∀ i, Stacks.Morphisms.IsFiniteLocallyFreeOfRank (ι i) (d i)] {ℓ : ℕ}
    (hd : ∀ i, (d i).Coprime ℓ) (hc : IsLimit c) {G : Sheaf (smallEtaleTopology S) Ab.{u + 1}}
    (hG : Stacks.Torsion.IsPrimePowerTorsion (smallEtaleTopology S) ℓ G) {n : ℕ}
    (hn : Nontrivial (Sheaf.H.{u + 1} G n)) :
    Stacks.Torsion.IsPrimePowerTorsion (smallEtaleTopology c.pt) ℓ
        ((smallEtalePullbackAb g).obj G) ∧
      Nontrivial (Sheaf.H.{u + 1} ((smallEtalePullbackAb g).obj G) n) :=
  ⟨isPrimePowerTorsion_smallEtalePullbackAb g hG,
    (injective_etaleCohomologyPullback_of_isLimit ι hι c g hg d hd hc hG n).nontrivial⟩

include hι hg in
/-- **[Stacks, Tag 0DV7].** Let `S` be a quasi-compact and quasi-separated scheme and let
`X = lim Xᵢ` be the limit of a directed system of `S`-schemes `ιᵢ : Xᵢ ⟶ S`, each finite étale of
constant degree `dᵢ` prime to `ℓ`, with structure morphism `g : X ⟶ S`. Then there is an
`ℓ`-power torsion sheaf `G` on `S_étale` with `Hⁿ(S, G) ≠ 0` if and only if there is an `ℓ`-power
torsion sheaf `F` on `X_étale` with `Hⁿ(X, F) ≠ 0`.

The source assumes that `ℓ` is prime and that `n > 0`; the proof uses neither. -/
@[stacks 0DV7 "(1) ⇔ (2)"]
theorem exists_isPrimePowerTorsion_nontrivial_sheafH_iff_of_isLimit [IsDirected I (· ≤ ·)]
    [Nonempty I] [CompactSpace S] [QuasiSeparatedSpace S] [∀ i, IsFinite (ι i)]
    [∀ i, Etale (ι i)] (d : Iᵒᵖ → ℕ) [∀ i, Stacks.Morphisms.IsFiniteLocallyFreeOfRank (ι i) (d i)]
    {ℓ : ℕ} (hd : ∀ i, (d i).Coprime ℓ) (hc : IsLimit c) (n : ℕ) :
    (∃ G : Sheaf (smallEtaleTopology S) Ab.{u + 1},
        Stacks.Torsion.IsPrimePowerTorsion (smallEtaleTopology S) ℓ G ∧
          Nontrivial (Sheaf.H.{u + 1} G n)) ↔
      ∃ F : Sheaf (smallEtaleTopology c.pt) Ab.{u + 1},
        Stacks.Torsion.IsPrimePowerTorsion (smallEtaleTopology c.pt) ℓ F ∧
          Nontrivial (Sheaf.H.{u + 1} F n) :=
  ⟨fun ⟨_, hG, hn⟩ => ⟨_, isPrimePowerTorsion_nontrivial_sheafH_smallEtalePullbackAb_of_isLimit
      ι hι c g hg d hd hc hG hn⟩,
    fun ⟨_, hF, hn⟩ => ⟨_, isPrimePowerTorsion_nontrivial_sheafH_smallEtalePushforwardAb_of_isLimit
      ι hι c g hg hc hF hn⟩⟩

end Stacks.EtaleCohomology

end
