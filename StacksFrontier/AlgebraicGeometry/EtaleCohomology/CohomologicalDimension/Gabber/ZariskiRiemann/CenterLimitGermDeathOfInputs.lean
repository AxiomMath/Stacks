module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.ZariskiRiemann.ValuationGermDeathOfLimitVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.ZariskiRiemann.ZariskiRiemannClosureModel
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.ZariskiRiemann.ZariskiRiemannCenterStrictHenselizationSystem

/-!
# Germ death at a valuation ring from vanishing on the limit: the assembly

This file proves `AlgebraicGeometry.Scheme.ZariskiRiemann.CenterLimitGermDeath` (Travaux de
Gabber, Exposé XVIII-A, last remark of §2) from three
precisely stated inputs.

Let `B` be a domain, `K = Frac B`, `V ⊆ K` a valuation ring dominating `B`, and `A_Y ⊆ V` the
image of the local ring at the center of `V` on a proper model `Y`
(`AlgebraicGeometry.Scheme.ZariskiRiemann.centerRanges`). A *center range system*
(`AlgebraicGeometry.Scheme.ZariskiRiemann.CenterRangeSystem`) is a directed system of
`A_Y`-algebras `R_Y` over the inclusions `A_Y ⊆ A_{Y'}`; its levels are the affine schemes
`X_Y = η ×_{Spec A_Y} Spec R_Y = Spec (K ⊗_{A_Y} R_Y)` (`CenterRangeSystem.level`), with
transition maps `X_{Y'} ⟶ X_Y` (`CenterRangeSystem.levelMap`). For the system of strict
henselizations `R_Y = A_Y^{sh}` (Stacks 04GI) the limit of the levels is
`Spec (K ⊗_V V^{sh})`. The inputs are:

* `AlgebraicGeometry.Scheme.ZariskiRiemann.CenterLevelEventualVanishing` (the limit layer, Steps
  2 and 4 of Gabber's proof, Stacks 09YQ): a class on a level whose restriction to the limit
  `Spec (K ⊗_V colim R_Y)` is zero dies on all sufficiently large levels;
* `AlgebraicGeometry.Scheme.ZariskiRiemann.CenterLevelStalkCompat` (Steps 0, 1 and 3, at
  algebraically closed geometric points): there is a system of strict henselizations, with
  colimit strictly henselian, local and ind-étale over `V`, such that every germ `γ` of
  `R^q j_* F` at `v̄ ≫ c_Y` comes from a class `c` on the level of `Y` and dies on every refinement
  `Y' ⟶ Y` with injective stalk map at the center on which `c` dies;
* `AlgebraicGeometry.Scheme.ZariskiRiemann.StalkTransitionSepClosedExtension`: germ death along a
  refinement at a separably closed geometric point may be checked after extending its field.

## Main definitions

* `AlgebraicGeometry.Scheme.ZariskiRiemann.CenterRangeSystem`, `CenterRangeSystem.level`,
  `CenterRangeSystem.levelMap`, `CenterRangeSystem.levelSheaf`, `CenterRangeSystem.colimit`.
* The three input statements above.

## Main results

* `AlgebraicGeometry.Scheme.ZariskiRiemann.centerLimitGermDeath_of_inputs`:
  the three inputs imply `CenterLimitGermDeath`.

## Implementation notes

Gabber's proof (Step 5) first passes to a refinement with injective
stalk map at the center and then uses the cocycle of the transition maps. Here the source model
is arbitrary: `CenterLevelStalkCompat` asks for a class on the level of the source model (a
strict henselization of `𝒪_{Y, y}` maps to one of its quotient `A_Y`), and only the target
refinement needs an injective stalk map; no cocycle of `stalkTransition` is used.

## References

* Travaux de Gabber sur l'uniformisation locale et la cohomologie étale des schémas
  quasi-excellents, Exposé XVIII-A (L. Illusie), last remark of §2, Astérisque 363–364 (2014)
* [Stacks Project, Tag 03Q9](https://stacks.math.columbia.edu/tag/03Q9)
* [Stacks Project, Tag 04GI](https://stacks.math.columbia.edu/tag/04GI)
* [Stacks Project, Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.StrictHenselization.DirectLimit
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Scheme.ZariskiRiemann

attribute [local instance high]
  Stacks.EtaleCohomology.ConstantTransport.hasExt_sheaf_smallEtaleTopology

open Stacks.EtaleCohomology

section System

variable {B : Type u} [CommRing B] [IsDomain B] (V : ValuationSubring (FractionRing B))
  (hV : ∀ b : B, algebraMap B (FractionRing B) b ∈ V)

/-- The center ranges `A_Y ⊆ V`, as a monotone family of subrings. -/
theorem centerRanges_monotone : Monotone fun a : centerRanges V hV => a.1 :=
  fun _ _ h => h

/-- **A center range system**: algebras `R_a` over the images `a = A_Y ⊆ V` of the local rings at
the centers of `V`, with ring maps `R_a → R_b` over the inclusions `A_Y ⊆ A_{Y'}` forming a
directed system. The strict henselizations of
`AlgebraicGeometry.Scheme.ZariskiRiemann.exists_isStrictHenselization_directLimit_centerRanges`
are one. -/
structure CenterRangeSystem where
  /-- The algebra over each `A_Y`. -/
  R : centerRanges V hV → Type u
  [commRing : ∀ a, CommRing (R a)]
  [algebra : ∀ a, Algebra a.1 (R a)]
  /-- The transition maps. -/
  f : ∀ a b, a ≤ b → R a →+* R b
  directedSystem : DirectedSystem R fun a b h => f a b h
  f_algebraMap : ∀ a b (hab : a ≤ b) (x : a.1), f a b hab (algebraMap a.1 (R a) x) =
    algebraMap b.1 (R b)
      (subringInclusion (fun a : centerRanges V hV => a.1) (centerRanges_monotone V hV) a b hab x)

attribute [instance] CenterRangeSystem.commRing CenterRangeSystem.algebra

namespace CenterRangeSystem

variable {V hV} (S : CenterRangeSystem V hV)

/-- The colimit `colim_a R_a` of a center range system. -/
abbrev colimit : Type u :=
  Ring.DirectLimit S.R fun a b h => S.f a b h

/-- The inclusion `A_Y ⊆ V ⊆ K` of a center range. -/
def toFractionRing (a : centerRanges V hV) : a.1 →+* FractionRing B :=
  (algebraMap V (FractionRing B)).comp a.1.subtype

/-- **The level** `X_a = η ×_{Spec A_Y} Spec R_a = Spec (K ⊗_{A_Y} R_a)` of a center range
system. -/
abbrev level (a : centerRanges V hV) : Scheme.{u} :=
  pullback (Spec.map (CommRingCat.ofHom (toFractionRing a)))
    (Spec.map (CommRingCat.ofHom (algebraMap a.1 (S.R a))))

/-- The projection `X_a ⟶ η` of a level. -/
def levelToGeneric (a : centerRanges V hV) : S.level a ⟶ Spec (.of (FractionRing B)) :=
  pullback.fst _ _

/-- **The transition map** `X_b ⟶ X_a` of the levels, for `a ≤ b`: the identity on `η` and
`Spec R_b ⟶ Spec R_a`. -/
def levelMap (a b : centerRanges V hV) (hab : a ≤ b) : S.level b ⟶ S.level a :=
  pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom (S.f a b hab)))
    (Spec.map (CommRingCat.ofHom
      (subringInclusion (fun a : centerRanges V hV => a.1) (centerRanges_monotone V hV) a b hab)))
    (by
      rw [Category.id_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      rfl)
    (by
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        ← CommRingCat.ofHom_comp]
      congr 2
      exact RingHom.ext fun x => (S.f_algebraMap a b hab x).symm)

/-- The transition maps of the levels lie over `η`. -/
@[reassoc]
theorem levelMap_levelToGeneric (a b : centerRanges V hV) (hab : a ≤ b) :
    S.levelMap a b hab ≫ S.levelToGeneric a = S.levelToGeneric b :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

/-- The pullback `F|_{X_a}` of an abelian sheaf on `η` to a level. -/
abbrev levelSheaf (F : Sheaf (Spec (.of (FractionRing B))).smallEtaleTopology AddCommGrpCat.{u + 1})
    (a : centerRanges V hV) : Sheaf (S.level a).smallEtaleTopology AddCommGrpCat.{u + 1} :=
  (etaleAbelianInverseImage.{u, 0} (S.levelToGeneric a)).obj F

end CenterRangeSystem

end System

/-- **The limit layer** (Steps 2 and 4 of Gabber's proof; Stacks 09YQ). Let `S` be
a center range system for a valuation ring `V` of `K = Frac B` containing `B`, and give its
colimit a `V`-algebra structure compatible with the maps `A_Y → R_a`. If
`H^q(Spec (colim R_a ⊗_V K), F|) = 0`, then every class `c ∈ H^q(X_a, F|)` on a level dies on all
sufficiently large levels: there is `b ≥ a` with `c ↦ 0` in `H^q(X_{b'}, ·)` for every `b' ≥ b`.

In the source: the levels are affine with affine transition maps, and their limit is
`Spec (colim_a (K ⊗_{A_a} R_a)) = Spec (K ⊗_V colim R_a)` since `V = colim A_a`
(`AlgebraicGeometry.Scheme.ZariskiRiemann.iSup_centerRanges`); a class vanishing on the limit
vanishes on some level (`Stacks.EtaleCohomology.LimitExt.exists_le_restriction_eq_zero_of_qcqs`),
hence on every later one. -/
def CenterLevelEventualVanishing : Prop :=
  ∀ (B : Type u) [CommRing B] [IsDomain B]
    (F : Sheaf (Spec (.of (FractionRing B))).smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (V : ValuationSubring (FractionRing B)) (hV : ∀ b : B, algebraMap B (FractionRing B) b ∈ V)
    (S : CenterRangeSystem V hV) [Algebra V S.colimit],
    (∀ (a : centerRanges V hV) (x : a.1), algebraMap V S.colimit x =
      Ring.DirectLimit.of S.R (fun a b h => S.f a b h) a (algebraMap a.1 (S.R a) x)) →
    Subsingleton (Sheaf.H.{u + 1}
      ((etaleAbelianInverseImage.{u, 0} (tensorFractionRingToGeneric V S.colimit)).obj F) q) →
    ∀ (a : centerRanges V hV) (c : Sheaf.H.{u + 1} (S.levelSheaf F a) q),
      ∃ b, a ≤ b ∧ ∀ (b' : centerRanges V hV) (hab' : a ≤ b'), b ≤ b' →
        etaleCohomologyRestrictionMap.{u, 0, u + 1} (S.levelMap a b' hab') _ q c = 0

/-- The center range `A_Y` of a model, as a member of
`AlgebraicGeometry.Scheme.ZariskiRiemann.centerRanges`. -/
def ProperModel.centerRangeMem {B : Type u} [CommRing B] [IsDomain B] (M : ProperModel B)
    (V : ValuationSubring (FractionRing B)) (hV : ∀ b : B, algebraMap B (FractionRing B) b ∈ V) :
    centerRanges V hV :=
  ⟨M.centerRange V hV, M, rfl⟩

/-- **Germs at the centers come from the levels** (Steps 0, 1 and 3
of Gabber's proof, at an algebraically closed geometric point). Let `V` dominate the domain `B` and let
`v̄ : Spec Ω ⟶ Spec V` be a geometric point at the closed point, `Ω` algebraically closed. There
are a center range system `S` and a `V`-algebra structure on its colimit, compatible with the
maps `A_Y → R_a`, such that the colimit is strictly henselian, local and ind-étale over `V`, and:
for every model `Y` and every germ `γ` of `R^q j_* F` at `v̄ ≫ c_Y` there is a class `c` on the
level `X_{A_Y}` such that every refinement `Y' ⟶ Y` whose stalk map at the center is injective
and on whose level `c` dies kills `γ`.

In the source: `S` is the system of strict henselizations `A_Y^{sh}` taken with respect to the
separable closure of `κ(V)` in `Ω` (`exists_isStrictHenselization_directLimit_centerRanges`); by
Stacks 03Q9 the germ is a class on `P_Y = η ×_Y Spec 𝒪^{sh}_{Y, v̄ ≫ c_Y}`, and the local map
`𝒪^{sh}_{Y,y} → A_Y^{sh}` over `𝒪_{Y,y} ↠ A_Y` gives `X_{A_Y} ⟶ P_Y`, along which `c` is its
restriction; for `Y'` with `𝒪_{Y',y'} ≅ A_{Y'}` the map `A_{Y'}^{sh} → 𝒪^{sh}_{Y',y'}` gives
`P_{Y'} ⟶ X_{A_{Y'}}`, and the composite `P_{Y'} ⟶ X_{A_{Y'}} ⟶ X_{A_Y} ⟶ P_Y` is the map of
strict henselizations along which the stalk transition is restriction (uniqueness, Stacks 04GU). -/
def CenterLevelStalkCompat : Prop :=
  ∀ (B : Type u) [CommRing B] [IsDomain B]
    (F : Sheaf (Spec (.of (FractionRing B))).smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (V : ValuationSubring (FractionRing B)) (hV : ∀ b : B, algebraMap B (FractionRing B) b ∈ V),
    IsLocalHom (valuationSubringBaseMap V hV) →
    ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (v : Spec (.of Ω) ⟶ Spec (.of V)),
      v (default : Spec (.of Ω)) = IsLocalRing.closedPoint V →
      ∃ (S : CenterRangeSystem V hV) (_ : Algebra V S.colimit),
        (∀ (a : centerRanges V hV) (x : a.1), algebraMap V S.colimit x =
          Ring.DirectLimit.of S.R (fun a b h => S.f a b h) a (algebraMap a.1 (S.R a) x)) ∧
        StrictlyHenselianLocalRing S.colimit ∧ IsLocalHom (algebraMap V S.colimit) ∧
        StacksDraft.IndEtale V S.colimit ∧
        ∀ (M : ProperModel B) (γ : (smallEtaleStalkAb (v ≫ M.center V hV)).obj
            (((etaleAbelianDirectImage.{u, 0} M.j).rightDerived q).obj F)),
          ∃ c : Sheaf.H.{u + 1} (S.levelSheaf F (M.centerRangeMem V hV)) q,
            ∀ (M' : ProperModel B) (φ : ProperModel.Refinement M' M),
              Function.Injective (M'.centerStalkMap V hV).hom →
              etaleCohomologyRestrictionMap.{u, 0, u + 1}
                  (S.levelMap (M.centerRangeMem V hV) (M'.centerRangeMem V hV)
                    (φ.centerRange_mono hV)) _ q c = 0 →
                (eqToHom (by rw [φ.center_eq hV, Category.assoc]) ≫
                  φ.stalkTransition F q (v ≫ M'.center V hV)) γ = 0

/-- The germ at the geometric point `s` of a section `x` of an abelian étale sheaf over an étale
neighbourhood `(U, w)` of `s`. -/
abbrev smallEtaleGerm {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ X) (G : Sheaf (smallEtaleTopology X) Ab.{u + 1}) (U : X.Etale)
    (w : (Scheme.pointSmallEtale s).fiber.obj U) (x : G.obj.obj (op U)) :
    (smallEtaleStalkAb s).obj G :=
  (Scheme.pointSmallEtale s).toPresheafFiber U w G.obj x

/-- **Germ death along a refinement survives extension of the geometric point.** Let
`π : Y' ⟶ Y` be a refinement, `s : Spec Ω ⟶ Y'` a geometric point with `Ω` separably closed,
`s₀ = s ≫ π`, `t : Spec Ω' ⟶ Spec Ω` with `Ω'` separably closed, and `sb = t ≫ s`,
`sb₀ = t ≫ s₀ = sb ≫ π`. If the germ at `sb₀` of a section `x` over an étale neighbourhood `(U, w)`
of `s₀` (through the lift `t ≫ w`) dies under the stalk transition at `sb`, then the germ of `x` at
`s₀` dies under the stalk transition at `s`.

In the source: the stalk of an étale sheaf at `s` is its stalk at `t ≫ s`, compatibly with
inverse images (an étale scheme over the separably closed `Ω` is a disjoint union of copies of
`Spec Ω`, so `s` and `t ≫ s` have the same étale neighbourhoods). -/
def StalkTransitionSepClosedExtension : Prop :=
  ∀ (B : Type u) [CommRing B] [IsDomain B]
    (F : Sheaf (Spec (.of (FractionRing B))).smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (M' M : ProperModel B) (φ : ProperModel.Refinement M' M)
    (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s₀ : Spec (.of Ω) ⟶ M.Y) (s : Spec (.of Ω) ⟶ M'.Y)
    (h : s₀ = s ≫ φ.π) (Ω' : Type u) [Field Ω'] [IsSepClosed Ω']
    (t : Spec (.of Ω') ⟶ Spec (.of Ω)) (sb₀ : Spec (.of Ω') ⟶ M.Y) (sb : Spec (.of Ω') ⟶ M'.Y)
    (hb₀ : sb₀ = sb ≫ φ.π), sb₀ = t ≫ s₀ → sb = t ≫ s →
    ∀ (U : M.Y.Etale) (w : (Scheme.pointSmallEtale s₀).fiber.obj U)
      (wb : (Scheme.pointSmallEtale sb₀).fiber.obj U), wb.left = t ≫ w.left →
      ∀ x : (((etaleAbelianDirectImage.{u, 0} M.j).rightDerived q).obj F).obj.obj (op U),
        (eqToHom (by rw [hb₀]) ≫ φ.stalkTransition F q sb) (smallEtaleGerm sb₀ _ U wb x) = 0 →
          (eqToHom (by rw [h]) ≫ φ.stalkTransition F q s) (smallEtaleGerm s₀ _ U w x) = 0

/-- **`CenterLimitGermDeath` from its three inputs** (Step 5 of Gabber's proof).
Extend the separably closed geometric point `v` to `v̄ = t ≫ v` with `Ω̄` an algebraic closure,
write the germ `γ` as the germ of a section `x`, and take the class `c` on the level of `Y` of
`CenterLevelStalkCompat` for the germ of `x` at `v̄ ≫ c_Y`. By `CenterLevelEventualVanishing`
(the colimit of the system being one of the rings `S` of the hypothesis) `c` dies on all levels
`≥ A_N` for some model `N`; the closure `Y'` of the generic point in `Y ×_B N` has
`A_{Y'} ⊇ A_Y, A_N` and injective stalk map at the center, so the refinement `Y' ⟶ Y` kills the
germ at `v̄`, hence, by `StalkTransitionSepClosedExtension`, the germ `γ` at `v`. -/
theorem centerLimitGermDeath_of_inputs (hlim : CenterLevelEventualVanishing.{u})
    (hcompat : CenterLevelStalkCompat.{u}) (hext : StalkTransitionSepClosedExtension.{u}) :
    CenterLimitGermDeath.{u} := by
  intro B _ _ F M q V hV hloc hvan Ω _ _ v hv γ
  let Ωbar := AlgebraicClosure Ω
  let t : Spec (.of Ωbar) ⟶ Spec (.of Ω) := Spec.map (CommRingCat.ofHom (algebraMap Ω Ωbar))
  have : Subsingleton ↥(Spec (CommRingCat.of Ωbar)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum Ωbar))
  have hvbar : (t ≫ v) (default : Spec (.of Ωbar)) = IsLocalRing.closedPoint V := by
    rw [Scheme.Hom.comp_apply, Subsingleton.elim (t default) default, hv]
  obtain ⟨S, algS, hpin, hsh, hlocS, hind, hS⟩ := hcompat B F q V hV hloc Ωbar (t ≫ v) hvbar
  have : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  obtain ⟨U, w, x, rfl⟩ :=
    (Scheme.pointSmallEtale (v ≫ M.center V hV)).toPresheafFiber_jointly_surjective
      (P := (((etaleAbelianDirectImage.{u, 0} M.j).rightDerived q).obj F).obj) γ
  let w' : Over.mk (v ≫ M.center V hV) ⟶ (Etale.forget M.Y).obj U := w
  let wb : (Scheme.pointSmallEtale ((t ≫ v) ≫ M.center V hV)).fiber.obj U :=
    Over.homMk (t ≫ w'.left) (by
      rw [Category.assoc]
      exact (congrArg (t ≫ ·) (Over.w w')).trans (Category.assoc _ _ _).symm)
  obtain ⟨c, hc⟩ := hS M (smallEtaleGerm _ _ U wb x)
  have hvanS : Subsingleton (Sheaf.H.{u + 1}
      ((etaleAbelianInverseImage.{u, 0} (tensorFractionRingToGeneric V S.colimit)).obj F) q) :=
    hvan S.colimit hind
  obtain ⟨b, -, hb⟩ := hlim B F q V hV S hpin hvanS (M.centerRangeMem V hV) c
  obtain ⟨N, hN⟩ := b.2
  let P := ProperModel.prod M N
  let M' := P.closureModel
  let φ : ProperModel.Refinement M' M := P.closureRefinement.comp (ProperModel.prodFst M N)
  have hbM' : b ≤ M'.centerRangeMem V hV := by
    change b.1 ≤ M'.centerRange V hV
    rw [← hN, P.centerRange_closureModel V hV]
    exact (ProperModel.prodSnd M N).centerRange_mono hV
  have hkill := hc M' φ (P.centerStalkMap_closureModel_injective V hV)
    (hb _ (φ.centerRange_mono hV) hbM')
  exact ⟨M', φ, hext B F q M' M φ Ω (v ≫ M.center V hV) (v ≫ M'.center V hV)
    (by rw [φ.center_eq hV]; simp only [Category.assoc]) Ωbar t ((t ≫ v) ≫ M.center V hV)
    ((t ≫ v) ≫ M'.center V hV) (by rw [φ.center_eq hV]; simp only [Category.assoc])
    (Category.assoc _ _ _) (Category.assoc _ _ _) U w wb rfl x hkill⟩

end AlgebraicGeometry.Scheme.ZariskiRiemann

end
