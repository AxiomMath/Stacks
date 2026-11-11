module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TerminalObjectFreeResolution
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedSupportEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ExtensionByZeroConservative
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisExtRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RestrictExtensionByZero
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SupportedOnComplement
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CohomologicalDescent.UnitAndCounitIsomorphisms
import StacksCore.Tactic.StacksAttribute

/-!
# The five clauses of Stacks 08GG

Let `(U ⊆ X, j : V ⟶ X)` be an elementary distinguished square of algebraic spaces over a
scheme `S`, let `P = U ×_X V` be its intersection and set `T = |X| \ |U|`.  Stacks 08GG says:

1. if `E` in `D(𝒪_X)` is supported on `T`, then (a) `E ⟶ Rj_*(E|_V)` and (b) `j_!(E|_V) ⟶ E`
   are isomorphisms;
2. if `F` in `D(𝒪_V)` is supported on `j^{-1}T`, then (a) `F ⟶ (j_!F)|_V`, (b)
   `(Rj_*F)|_V ⟶ F` and (c) `j_!F ⟶ Rj_*F` are isomorphisms.

## Main results

* `AlgebraicGeometry.Space.isIso_unit_derivedRestrict_of_cohomologySupportedOn`:
  **clause (1)(a)**, the unit `E ⟶ Rj_*(E|_V)` of `(-)|_V ⊣ Rj_*`.
* `AlgebraicGeometry.Space.isIso_counit_derivedRestrict_of_cohomologySupportedOn`:
  **clause (1)(b)**, the counit `j_!(E|_V) ⟶ E` of `j_! ⊣ (-)|_V`.
* `AlgebraicGeometry.Space.isIso_unit_derivedShriek_of_cohomologySupportedOn`:
  **clause (2)(a)**, the unit `F ⟶ (j_!F)|_V` of `j_! ⊣ (-)|_V`.
* `AlgebraicGeometry.Space.isIso_counit_derivedPushforward_of_cohomologySupportedOn`:
  **clause (2)(b)**, the counit `(Rj_*F)|_V ⟶ F` of `(-)|_V ⊣ Rj_*`.
* `AlgebraicGeometry.Space.isIso_supportedShriekToPushforward_of_supported`:
  **clause (2)(c)**, the comparison `j_!F ⟶ Rj_*F` of
  `AlgebraicGeometry.Space.supportedShriekToPushforward`.
* `AlgebraicGeometry.Space.isIso_of_cohomologySupportedOn_edsEtale`: **Stacks 08GG**, all
  five clauses together.

## The argument

*Part (1).*  If `E|_U = 0` and `E|_P = 0`, the Mayer–Vietoris long exact sequence of Stacks 08H9,
`AlgebraicGeometry.Space.mayerVietoris_shiftedHom_longExactSequence_restrictions`, read at
`Hom(G, E[n])` or at `Hom(E, G[n])`, has every group over `U` and over `P` zero, so restriction
`Hom(G, E[n]) ⟶ Hom(G|_V, E|_V[n])` (respectively `Hom(E, G[n]) ⟶ Hom(E|_V, G|_V[n])`) is
bijective for every `G` (`AlgebraicGeometry.Space.bijective_map_edsEtale_of_isZero_target`,
`AlgebraicGeometry.Space.bijective_map_edsEtale_of_isZero_source`).  By the
Yoneda lemma that bijectivity is exactly the invertibility of the unit at `E` of any right
adjoint of restriction, respectively of the counit at `E` of any left adjoint
(`CategoryTheory.Adjunction.isIso_unit_app_of_bijective_map`,
`CategoryTheory.Adjunction.isIso_counit_app_of_bijective_map`).  Support of `E` on `T` gives
`E|_U = 0` and `E|_P = 0` by
`AlgebraicGeometry.Space.isZero_etaleModulePullback_mapDerivedCategory_of_range_subset` (Stacks
04K5 and the commutation of an exact functor with cohomology).

*Clause (2)(a).*  `F` supported on `j^{-1}T` restricts to zero on `P`; by Stacks 08HA at the
cartesian square `P = U ×_X V`, `(j_!F)|_U = p_!(F|_P) = 0`, so `j_!F` is supported on `T`.
Clause (1)(b) at `j_!F` and the triangle identity make `j_!` of the unit at `F` invertible, and
`j_!` reflects isomorphisms
(`AlgebraicGeometry.Space.isIso_of_isIso_mapDerivedCategory_map_leftAdjoint_etaleModulePullback`).

*Clauses (2)(b) and (2)(c).*  Clause (1)(a) at `j_!F` inverts `η : j_!F ⟶ Rj_*((j_!F)|_V)`.  The
triangle identity `η|_V ≫ ε = 𝟙` then inverts the counit `ε` at `(j_!F)|_V`, which is
isomorphic to `F` by clause (2)(a), so `ε` is invertible at `F`: clause (2)(b).  The comparison
of clause (2)(c) is `η ≫ Rj_*(u⁻¹)` with `u` the unit of clause (2)(a), a composite of two
isomorphisms.

## Implementation notes

*`j_!` and `Rj_*` are given by their adjunctions.*  Derived extension by zero is an arbitrary
left adjoint, and derived direct image an arbitrary right adjoint, of derived restriction
`(-)|_V : D(𝒪_X) ⥤ D(𝒪_V)`; the unit and counit maps of the source are the unit and counit of
those adjunctions.  An adjoint is determined up to a unique compatible isomorphism by its
adjunction, so this pins both functors and all four maps; the statements are therefore about
every such pair, which includes the canonical ones.  Both exist: `j_!` is
`(AlgebraicGeometry.Space.etaleModuleLowerShriekAdjunction _ _ _ j hj).mapDerivedCategory`, and
a total right derived functor of the direct image is right adjoint to derived restriction by
`AlgebraicGeometry.Space.etaleModulePullbackDerivedPushforwardAdjunction`.

*Universes and instances.*  The module universe is that of the schemes, where the sheafification
instances of the small étale sites are found by instance search, so no instance binder is
carried.

## References

* [Stacks Project, Tag 08GG](https://stacks.math.columbia.edu/tag/08GG)
* [Stacks Project, Tag 08H9](https://stacks.math.columbia.edu/tag/08H9)
* [Stacks Project, Tag 08HA](https://stacks.math.columbia.edu/tag/08HA)
* [Stacks Project, Tag 04K5](https://stacks.math.columbia.edu/tag/04K5)
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits Pretriangulated

universe v₁ v₂ u₁ u₂ u

namespace CategoryTheory.Adjunction

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- **The Yoneda criterion for the unit of an adjunction.**  If `M` induces a bijection
`(G ⟶ E) ≃ (M G ⟶ M E)` for every `G`, then the unit `E ⟶ R (M E)` of any adjunction `M ⊣ R`
is an isomorphism: composition with it is that bijection followed by the adjunction bijection. -/
theorem isIso_unit_app_of_bijective_map {M : C ⥤ D} {R : D ⥤ C} (adj : M ⊣ R) (E : C)
    (h : ∀ G : C, Function.Bijective (fun g : G ⟶ E => M.map g)) :
    IsIso (adj.unit.app E) := by
  refine isIso_of_yoneda_map_bijective _ fun G => ?_
  have heq : (fun x : G ⟶ E => x ≫ adj.unit.app E) =
      (adj.homEquiv G (M.obj E)) ∘ (fun g : G ⟶ E => M.map g) := by
    funext x
    simp only [Function.comp_apply, Adjunction.homEquiv_unit]
    exact (adj.unit_naturality x).symm
  have hb := (adj.homEquiv G (M.obj E)).bijective.comp (h G)
  rw [← heq] at hb
  exact hb

/-- If the counit of `L ⊣ R` is invertible at `L X`, then `L` of the unit at `X` is invertible:
by the triangle identity it is the inverse of that counit. -/
theorem isIso_map_unit_app_of_isIso_counit_app {L : D ⥤ C} {R : C ⥤ D} (adj : L ⊣ R) (X : D)
    [IsIso (adj.counit.app (L.obj X))] : IsIso (L.map (adj.unit.app X)) := by
  have : IsIso (L.map (adj.unit.app X) ≫ adj.counit.app (L.obj X)) := by
    rw [adj.left_triangle_components X]
    exact ⟨⟨𝟙 _, Category.comp_id _, Category.comp_id _⟩⟩
  exact IsIso.of_isIso_comp_right _ (adj.counit.app (L.obj X))

end CategoryTheory.Adjunction

namespace CategoryTheory.ShiftedHom

/-- A functor commuting with shifts is bijective on morphisms `X ⟶ Y` as soon as it is
bijective on the shifted morphisms of degree `0`. -/
theorem bijective_map_of_bijective_map_zero {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] [HasShift C ℤ] [HasShift D ℤ] (F : C ⥤ D) [F.CommShift ℤ] {X Y : C}
    (h : Function.Bijective (fun x : ShiftedHom X Y (0 : ℤ) => x.map F)) :
    Function.Bijective (fun g : X ⟶ Y => F.map g) := by
  have key : ∀ g : X ⟶ Y,
      (ShiftedHom.homEquiv (X := F.obj X) (Y := F.obj Y) (0 : ℤ) rfl).symm
        ((ShiftedHom.homEquiv (X := X) (Y := Y) (0 : ℤ) rfl g).map F) = F.map g := by
    intro g
    rw [Equiv.symm_apply_eq, ShiftedHom.homEquiv_apply, ShiftedHom.homEquiv_apply,
      ShiftedHom.map_mk₀]
  have hb := (ShiftedHom.homEquiv (X := F.obj X) (Y := F.obj Y) (0 : ℤ) rfl).symm.bijective.comp
    (h.comp (ShiftedHom.homEquiv (X := X) (Y := Y) (0 : ℤ) rfl).bijective)
  have heq : (fun g : X ⟶ Y => F.map g) =
      (ShiftedHom.homEquiv (X := F.obj X) (Y := F.obj Y) (0 : ℤ) rfl).symm ∘
        (fun x : ShiftedHom X Y (0 : ℤ) => x.map F) ∘
          (ShiftedHom.homEquiv (X := X) (Y := Y) (0 : ℤ) rfl) :=
    funext fun g => (key g).symm
  rw [heq]
  exact hb

end CategoryTheory.ShiftedHom

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] HasDerivedCategory.standard etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback
  smallEtaleRingedSite_hasSheafify_addCommGrpCat
  smallEtaleRingedSite_wEqualsLocallyBijective_addCommGrpCat

section Square

variable {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)

/-- **Restriction to the étale space of an elementary distinguished square is bijective on
shifted morphisms whose groups over the open subspace and over the intersection vanish.**  Let
`G` and `E` be objects of `D(𝒪_X)` such that every shifted morphism `G|_U ⟶ E|_U[m]` and
`G|_P ⟶ E|_P[m]` is zero.  Then restriction `Hom(G, E[m]) ⟶ Hom(G|_V, E|_V[m])` is bijective.

This is the Mayer–Vietoris long exact sequence of Stacks 08H9: its terms over `U` and `P`
vanish, so injectivity is the exactness at `Hom(G, E[m])` after the boundary out of the zero
group over `P` in degree `m - 1`, and surjectivity is the exactness at the sum, the difference
map landing in the zero group over `P` in degree `m`. -/
theorem bijective_shiftedHomMap_edsEtale_of_forall_eq_zero
    (G E : DerivedCategory (Modules.{u, u} B S hS W.1 W.2))
    (hU : ∀ (m : ℤ) (x : (etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
        (isEtale_edsOpenHom B S hS hsq)).mapDerivedCategory.obj G ⟶
        ((etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
          (isEtale_edsOpenHom B S hS hsq)).mapDerivedCategory.obj E)⟦m⟧), x = 0)
    (hP : ∀ (m : ℤ) (x : (etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
        (isEtale_edsInterHom B S hS hsq)).mapDerivedCategory.obj G ⟶
        ((etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
          (isEtale_edsInterHom B S hS hsq)).mapDerivedCategory.obj E)⟦m⟧), x = 0)
    (m : ℤ) :
    Function.Bijective (fun x : G ⟶ E⟦m⟧ => ShiftedHom.map x
      (etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
        (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  obtain ⟨δ, hδ⟩ := exists_mem_distTriang_edsDerivedShriekMayerVietoris B S hS hsq
    (etaleModuleLowerShriekAdjunction B S hS (edsOpenHom B S hS hsq)
      (isEtale_edsOpenHom B S hS hsq))
    (etaleModuleLowerShriekAdjunction B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq))
    (etaleModuleLowerShriekAdjunction B S hS (edsInterHom B S hS hsq)
      (isEtale_edsInterHom B S hS hsq)) G
  have hL := fun k : ℤ => mayerVietoris_shiftedHom_longExactSequence_restrictions
    (etaleModuleLowerShriekAdjunction B S hS (edsOpenHom B S hS hsq)
      (isEtale_edsOpenHom B S hS hsq))
    (etaleModuleLowerShriekAdjunction B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq))
    (etaleModuleLowerShriekAdjunction B S hS (edsInterHom B S hS hsq)
      (isEtale_edsInterHom B S hS hsq))
    (edsShriekOpenComparison B S hS hsq _ _) (edsShriekEtaleComparison B S hS hsq _ _)
    (edsShriekOpenComparison_comp_counit B S hS hsq _ _)
    (edsShriekEtaleComparison_comp_counit B S hS hsq _ _) G E δ hδ k
  constructor
  · intro x y hxy
    have hsub : ShiftedHom.map (x - y)
        (etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
          (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory = 0 := by
      simp only [ShiftedHom.map, Functor.map_sub, Preadditive.sub_comp] at hxy ⊢
      rw [hxy, sub_self]
    obtain ⟨z, hz⟩ := ((hL n).2.2 (x - y)).1 (Prod.ext (hU _ _) hsub)
    rw [hP n z, map_zero] at hz
    exact sub_eq_zero.1 hz.symm
  · intro yV
    obtain ⟨x, hx⟩ := ((hL (n + 1)).1 (0, yV)).1 (hP _ _)
    exact ⟨x, congrArg Prod.snd hx⟩

/-- **Restriction to the étale space is bijective on morphisms into an object vanishing over
the open subspace and over the intersection.**  If `E|_U = 0` and `E|_P = 0`, then
`G ⟶ E` and `G|_V ⟶ E|_V` correspond bijectively under restriction, for every `G`. -/
theorem bijective_map_edsEtale_of_isZero_target
    (G E : DerivedCategory (Modules.{u, u} B S hS W.1 W.2))
    (hU : IsZero ((etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
      (isEtale_edsOpenHom B S hS hsq)).mapDerivedCategory.obj E))
    (hP : IsZero ((etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
      (isEtale_edsInterHom B S hS hsq)).mapDerivedCategory.obj E)) :
    Function.Bijective (fun g : G ⟶ E =>
      (etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
        (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory.map g) :=
  ShiftedHom.bijective_map_of_bijective_map_zero _
    (bijective_shiftedHomMap_edsEtale_of_forall_eq_zero B S hS hsq G E
      (fun m _ => ((shiftFunctor _ m).map_isZero hU).eq_of_tgt _ _)
      (fun m _ => ((shiftFunctor _ m).map_isZero hP).eq_of_tgt _ _) 0)

/-- **Restriction to the étale space is bijective on morphisms out of an object vanishing over
the open subspace and over the intersection.**  If `E|_U = 0` and `E|_P = 0`, then
`E ⟶ G` and `E|_V ⟶ G|_V` correspond bijectively under restriction, for every `G`. -/
theorem bijective_map_edsEtale_of_isZero_source
    (E G : DerivedCategory (Modules.{u, u} B S hS W.1 W.2))
    (hU : IsZero ((etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
      (isEtale_edsOpenHom B S hS hsq)).mapDerivedCategory.obj E))
    (hP : IsZero ((etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
      (isEtale_edsInterHom B S hS hsq)).mapDerivedCategory.obj E)) :
    Function.Bijective (fun g : E ⟶ G =>
      (etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
        (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory.map g) :=
  ShiftedHom.bijective_map_of_bijective_map_zero _
    (bijective_shiftedHomMap_edsEtale_of_forall_eq_zero B S hS hsq E G
      (fun _ _ => hU.eq_of_src _ _) (fun _ _ => hP.eq_of_src _ _) 0)

/-- **An object of `D(𝒪_X)` supported on `T = |X| \ |U|` restricts to zero on the open
subspace and on the intersection.** -/
theorem isZero_edsOpen_and_edsInter_of_cohomologySupportedOn
    (E : DerivedCategory (Modules.{u, u} B S hS W.1 W.2))
    (hE : CohomologySupportedOn B S hS W.1 W.2 (edsComplementPoints B S hS Uo) E) :
    IsZero ((etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
        (isEtale_edsOpenHom B S hS hsq)).mapDerivedCategory.obj E) ∧
      IsZero ((etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
        (isEtale_edsInterHom B S hS hsq)).mapDerivedCategory.obj E) :=
  ⟨isZero_etaleModulePullback_mapDerivedCategory_of_range_subset B S hS
      (edsOpenHom B S hS hsq) (isEtale_edsOpenHom B S hS hsq) E hE
      (range_pointsMap_edsOpenHom B S hS hsq).subset,
    isZero_etaleModulePullback_mapDerivedCategory_of_range_subset B S hS
      (edsInterHom B S hS hsq) (isEtale_edsInterHom B S hS hsq) E hE
      (range_pointsMap_edsInterHom_subset B S hS hsq)⟩

/-- Let `(U ⊆ X, j : V ⟶ X)` be an elementary distinguished square of algebraic spaces over a
scheme `S` and set `T = |X| \ |U|`.  Let `Rj_*` be a right adjoint of derived restriction
`(-)|_V : D(𝒪_X) ⥤ D(𝒪_V)`.  If `E` in `D(𝒪_X)` is supported on `T`, then the unit
`E ⟶ Rj_*(E|_V)` is an isomorphism. -/
@[stacks 08GG "clause (1)(a): for E in D(O_X) supported on T = |X| \\ |U| the map
E ⟶ Rj_*(E|_V), the unit of the adjunction between derived restriction and the derived direct
image, is an isomorphism. Rj_* is any right adjoint of derived restriction, which pins it and its
unit; a total right derived functor of j_* is one, by
etaleModulePullbackDerivedPushforwardAdjunction"]
theorem isIso_unit_derivedRestrict_of_cohomologySupportedOn
    {RpushD : DerivedCategory (Modules.{u, u} B S hS (edsEtale B S hS hsq).1
        (edsEtale B S hS hsq).2) ⥤ DerivedCategory (Modules.{u, u} B S hS W.1 W.2)}
    (adjPush : (etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory ⊣ RpushD)
    (E : DerivedCategory (Modules.{u, u} B S hS W.1 W.2))
    (hE : CohomologySupportedOn B S hS W.1 W.2 (edsComplementPoints B S hS Uo) E) :
    IsIso (adjPush.unit.app E) :=
  have h := isZero_edsOpen_and_edsInter_of_cohomologySupportedOn B S hS hsq E hE
  Adjunction.isIso_unit_app_of_bijective_map adjPush E fun G =>
    bijective_map_edsEtale_of_isZero_target B S hS hsq G E h.1 h.2

/-- Let `(U ⊆ X, j : V ⟶ X)` be an elementary distinguished square of algebraic spaces over a
scheme `S` and set `T = |X| \ |U|`.  Let `j_!` be a left adjoint of derived restriction
`(-)|_V : D(𝒪_X) ⥤ D(𝒪_V)`.  If `E` in `D(𝒪_X)` is supported on `T`, then the counit
`j_!(E|_V) ⟶ E` is an isomorphism. -/
@[stacks 08GG "clause (1)(b): for E in D(O_X) supported on T = |X| \\ |U| the map
j_!(E|_V) ⟶ E, the counit of the adjunction between derived extension by zero and derived
restriction, is an isomorphism. j_! is any left adjoint of derived restriction, which pins it and
its counit; the derived functor of etaleModuleLowerShriek is one"]
theorem isIso_counit_derivedRestrict_of_cohomologySupportedOn
    {shriekD : DerivedCategory (Modules.{u, u} B S hS (edsEtale B S hS hsq).1
        (edsEtale B S hS hsq).2) ⥤ DerivedCategory (Modules.{u, u} B S hS W.1 W.2)}
    (adjShriek : shriekD ⊣ (etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory)
    (E : DerivedCategory (Modules.{u, u} B S hS W.1 W.2))
    (hE : CohomologySupportedOn B S hS W.1 W.2 (edsComplementPoints B S hS Uo) E) :
    IsIso (adjShriek.counit.app E) :=
  have h := isZero_edsOpen_and_edsInter_of_cohomologySupportedOn B S hS hsq E hE
  Adjunction.isIso_counit_app_of_bijective_map adjShriek E fun G =>
    bijective_map_edsEtale_of_isZero_source B S hS hsq E G h.1 h.2

/-- **The image of the points of the intersection of an elementary distinguished square lies
over the open subspace.** -/
theorem range_pointsMap_edsSnd_subset_preimage :
    Set.range (pointsMap B S hS (edsInter B S hS hsq).1 (edsSnd B S hS hsq).hom) ⊆
      pointsMap B S hS (edsEtale B S hS hsq).1 (edsEtaleHom B S hS hsq).hom ⁻¹'
        Set.range (pointsMap B S hS Uo.toFunctor Uo.ι) := by
  have hw : (edsInterHom B S hS hsq).hom =
      (edsSnd B S hS hsq).hom ≫ (edsEtaleHom B S hS hsq).hom :=
    congrArg (fun m : edsInter B S hS hsq ⟶ W => m.hom)
      (isPullback_edsInter B S hS hsq).w
  rintro _ ⟨p, rfl⟩
  refine range_pointsMap_edsInterHom_subset B S hS hsq ⟨p, ?_⟩
  rw [hw, pointsMap_comp]
  rfl

/-- **An object of `D(𝒪_V)` supported on `j^{-1}T` restricts to zero on the intersection.** -/
theorem isZero_edsRestrictSnd_of_cohomologySupportedOn
    (F : DerivedCategory (Modules.{u, u} B S hS (edsEtale B S hS hsq).1
      (edsEtale B S hS hsq).2))
    (hF : CohomologySupportedOn B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2
      (edsEtalePreimageComplementPoints B S hS hsq) F) :
    IsZero ((etaleModulePullback.{u, u} B S hS (edsSnd B S hS hsq)
      (isEtale_edsSnd B S hS hsq)).mapDerivedCategory.obj F) :=
  isZero_etaleModulePullback_mapDerivedCategory_of_disjoint B S hS
    (edsSnd B S hS hsq) (isEtale_edsSnd B S hS hsq) _ F hF
    (Set.disjoint_left.mpr fun _ hx hmem =>
      hmem (range_pointsMap_edsSnd_subset_preimage B S hS hsq hx))

/-- **The extension by zero of an object of `D(𝒪_V)` supported on `j^{-1}T` is supported on
`T = |X| \ |U|`.**  Its restriction to `P` vanishes, so Stacks 08HA at the cartesian square
`P = U ×_X V` makes `(j_!F)|_U ≅ p_!(F|_P)` vanish. -/
theorem cohomologySupportedOn_lowerShriek_of_cohomologySupportedOn
    (F : DerivedCategory (Modules.{u, u} B S hS (edsEtale B S hS hsq).1
      (edsEtale B S hS hsq).2))
    (hF : CohomologySupportedOn B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2
      (edsEtalePreimageComplementPoints B S hS hsq) F) :
    CohomologySupportedOn B S hS W.1 W.2 (edsComplementPoints B S hS Uo)
      ((etaleModuleLowerShriek B S hS (edsEtaleHom B S hS hsq)
        (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory.obj F) := by
  have hbc := isIso_derivedRestrictExtensionByZeroMap B S hS
    (isPullback_edsInter B S hS hsq) (isEtale_edsEtaleHom B S hS hsq)
    (isEtale_edsOpenHom B S hS hsq)
    (etaleModuleLowerShriekAdjunction B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq))
    (etaleModuleLowerShriekAdjunction B S hS (edsFst B S hS hsq) (isEtale_edsFst B S hS hsq))
  have hvan : IsZero ((etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
      (isEtale_edsOpenHom B S hS hsq)).mapDerivedCategory.obj
      ((etaleModuleLowerShriek B S hS (edsEtaleHom B S hS hsq)
        (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory.obj F)) :=
    ((etaleModuleLowerShriek B S hS (edsFst B S hS hsq)
        (isEtale_edsFst B S hS hsq)).mapDerivedCategory.map_isZero
          (isZero_edsRestrictSnd_of_cohomologySupportedOn B S hS hsq F hF)).of_iso
      ((@asIso _ _ _ _ _ hbc).app F).symm
  exact cohomologySupportedOn_compl_range_of_isZero_etaleModulePullback B S hS
    (edsOpenHom B S hS hsq) (isEtale_edsOpenHom B S hS hsq) _ hvan

/-- **Clause (2)(a) of Stacks 08GG at the canonical derived extension by zero.**  The unit
`F ⟶ (j_!F)|_V` of the derived adjunction of `etaleModuleLowerShriekAdjunction` is invertible at
`F` supported on `j^{-1}T`: clause (1)(b) at `j_!F` inverts the counit there, the triangle
identity then inverts `j_!` of the unit, and `j_!` reflects isomorphisms. -/
theorem isIso_unit_mapDerivedCategory_lowerShriek_of_cohomologySupportedOn
    (F : DerivedCategory (Modules.{u, u} B S hS (edsEtale B S hS hsq).1
      (edsEtale B S hS hsq).2))
    (hF : CohomologySupportedOn B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2
      (edsEtalePreimageComplementPoints B S hS hsq) F) :
    IsIso ((etaleModuleLowerShriekAdjunction B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory.unit.app F) := by
  have hcounit := isIso_counit_derivedRestrict_of_cohomologySupportedOn B S hS hsq
    (etaleModuleLowerShriekAdjunction B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory _
    (cohomologySupportedOn_lowerShriek_of_cohomologySupportedOn B S hS hsq F hF)
  have hmap := Adjunction.isIso_map_unit_app_of_isIso_counit_app
    (etaleModuleLowerShriekAdjunction B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory F
  exact isIso_of_isIso_mapDerivedCategory_map_leftAdjoint_etaleModulePullback B S hS
    (edsEtaleHom B S hS hsq) (isEtale_edsEtaleHom B S hS hsq)
    (etaleModuleLowerShriekAdjunction B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq)) _ hmap

/-- Let `(U ⊆ X, j : V ⟶ X)` be an elementary distinguished square of algebraic spaces over a
scheme `S` and set `T = |X| \ |U|`.  Let `j_!` be a left adjoint of derived restriction
`(-)|_V : D(𝒪_X) ⥤ D(𝒪_V)`.  If `F` in `D(𝒪_V)` is supported on `j^{-1}T`, then the unit
`F ⟶ (j_!F)|_V` is an isomorphism. -/
@[stacks 08GG "clause (2)(a): for F in D(O_V) supported on the preimage of T = |X| \\ |U| the map
F ⟶ (j_!F)|_V, the unit of the adjunction between derived extension by zero and derived
restriction, is an isomorphism. j_! is any left adjoint of derived restriction, which pins it and
its unit; the derived functor of etaleModuleLowerShriek is one"]
theorem isIso_unit_derivedShriek_of_cohomologySupportedOn
    {shriekD : DerivedCategory (Modules.{u, u} B S hS (edsEtale B S hS hsq).1
        (edsEtale B S hS hsq).2) ⥤ DerivedCategory (Modules.{u, u} B S hS W.1 W.2)}
    (adjShriek : shriekD ⊣ (etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory)
    (F : DerivedCategory (Modules.{u, u} B S hS (edsEtale B S hS hsq).1
      (edsEtale B S hS hsq).2))
    (hF : CohomologySupportedOn B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2
      (edsEtalePreimageComplementPoints B S hS hsq) F) :
    IsIso (adjShriek.unit.app F) := by
  have hcanon := isIso_unit_mapDerivedCategory_lowerShriek_of_cohomologySupportedOn
    B S hS hsq F hF
  rw [← Adjunction.unit_leftAdjointUniq_hom_app adjShriek] at hcanon
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ inferInstance hcanon

/-- **Clause (1)(a) of Stacks 08GG at the extension by zero of an object supported on
`j^{-1}T`**, for an arbitrary left adjoint `j_!` of derived restriction: `j_!F` is isomorphic to
the canonical extension by zero, which is supported on `T`, and the unit of `(-)|_V ⊣ Rj_*` is
natural. -/
theorem isIso_unit_derivedRestrict_shriek_of_cohomologySupportedOn
    {shriekD RpushD : DerivedCategory (Modules.{u, u} B S hS (edsEtale B S hS hsq).1
        (edsEtale B S hS hsq).2) ⥤ DerivedCategory (Modules.{u, u} B S hS W.1 W.2)}
    (adjShriek : shriekD ⊣ (etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory)
    (adjPush : (etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory ⊣ RpushD)
    (F : DerivedCategory (Modules.{u, u} B S hS (edsEtale B S hS hsq).1
      (edsEtale B S hS hsq).2))
    (hF : CohomologySupportedOn B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2
      (edsEtalePreimageComplementPoints B S hS hsq) F) :
    IsIso (adjPush.unit.app (shriekD.obj F)) := by
  rw [NatTrans.isIso_app_iff_of_iso adjPush.unit
    ((Adjunction.leftAdjointUniq adjShriek
      (etaleModuleLowerShriekAdjunction B S hS (edsEtaleHom B S hS hsq)
        (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory).app F)]
  exact isIso_unit_derivedRestrict_of_cohomologySupportedOn B S hS hsq adjPush _
    (cohomologySupportedOn_lowerShriek_of_cohomologySupportedOn B S hS hsq F hF)

/-- Let `(U ⊆ X, j : V ⟶ X)` be an elementary distinguished square of algebraic spaces over a
scheme `S` and set `T = |X| \ |U|`.  Let `Rj_*` be a right adjoint of derived restriction
`(-)|_V : D(𝒪_X) ⥤ D(𝒪_V)`.  If `F` in `D(𝒪_V)` is supported on `j^{-1}T`, then the counit
`(Rj_*F)|_V ⟶ F` is an isomorphism. -/
@[stacks 08GG "clause (2)(b): for F in D(O_V) supported on the preimage of T = |X| \\ |U| the
map (Rj_*F)|_V ⟶ F, the counit of the adjunction between derived restriction and the derived
direct image, is an isomorphism. Rj_* is any right adjoint of derived restriction, which pins it
and its counit; a total right derived functor of j_* is one, by
etaleModulePullbackDerivedPushforwardAdjunction"]
theorem isIso_counit_derivedPushforward_of_cohomologySupportedOn
    {RpushD : DerivedCategory (Modules.{u, u} B S hS (edsEtale B S hS hsq).1
        (edsEtale B S hS hsq).2) ⥤ DerivedCategory (Modules.{u, u} B S hS W.1 W.2)}
    (adjPush : (etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory ⊣ RpushD)
    (F : DerivedCategory (Modules.{u, u} B S hS (edsEtale B S hS hsq).1
      (edsEtale B S hS hsq).2))
    (hF : CohomologySupportedOn B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2
      (edsEtalePreimageComplementPoints B S hS hsq) F) :
    IsIso (adjPush.counit.app F) := by
  have hunit : IsIso ((etaleModuleLowerShriekAdjunction B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory.unit.app F) :=
    isIso_unit_mapDerivedCategory_lowerShriek_of_cohomologySupportedOn B S hS hsq F hF
  have hη := isIso_unit_derivedRestrict_of_cohomologySupportedOn B S hS hsq adjPush _
    (cohomologySupportedOn_lowerShriek_of_cohomologySupportedOn B S hS hsq F hF)
  have hε := Adjunction.isIso_counit_app_obj_of_isIso_unit_app adjPush
    ((etaleModuleLowerShriek B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory.obj F) hη
  exact (NatTrans.isIso_app_iff_of_iso adjPush.counit
    (asIso ((etaleModuleLowerShriekAdjunction B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory.unit.app F))).2 hε

/-- Let `(U ⊆ X, j : V ⟶ X)` be an elementary distinguished square of algebraic spaces over a
scheme `S` and set `T = |X| \ |U|`.  Let `j_!` and `Rj_*` be a left and a right adjoint of
derived restriction `(-)|_V : D(𝒪_X) ⥤ D(𝒪_V)`.  If `F` in `D(𝒪_V)` is supported on `j^{-1}T`,
then the comparison `j_!F ⟶ Rj_*F` (`AlgebraicGeometry.Space.supportedShriekToPushforward`) is
an isomorphism. -/
@[stacks 08GG "clause (2)(c): for F in D(O_V) supported on the preimage of T = |X| \\ |U| the
comparison j_!F ⟶ Rj_*F is an isomorphism. The comparison is supportedShriekToPushforward, the
adjunct under derived restriction ⊣ Rj_* of the inverse of the unit F ⟶ (j_!F)|_V, which is
invertible by clause (2)(a), isIso_unit_derivedShriek_of_cohomologySupportedOn. j_! and Rj_* are
any left and right adjoints of derived restriction"]
theorem isIso_supportedShriekToPushforward_of_supported
    {shriekD RpushD : DerivedCategory (Modules.{u, u} B S hS (edsEtale B S hS hsq).1
        (edsEtale B S hS hsq).2) ⥤ DerivedCategory (Modules.{u, u} B S hS W.1 W.2)}
    (adjShriek : shriekD ⊣ (etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory)
    (adjPush : (etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory ⊣ RpushD)
    (F : DerivedCategory (Modules.{u, u} B S hS (edsEtale B S hS hsq).1
      (edsEtale B S hS hsq).2))
    (hF : CohomologySupportedOn B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2
      (edsEtalePreimageComplementPoints B S hS hsq) F) :
    IsIso (supportedShriekToPushforward B S hS hsq adjShriek adjPush F
      (isIso_unit_derivedShriek_of_cohomologySupportedOn B S hS hsq adjShriek F hF)) := by
  have := isIso_unit_derivedShriek_of_cohomologySupportedOn B S hS hsq adjShriek F hF
  have := isIso_unit_derivedRestrict_shriek_of_cohomologySupportedOn B S hS hsq adjShriek
    adjPush F hF
  unfold supportedShriekToPushforward
  rw [Adjunction.homEquiv_unit]
  infer_instance

/-- Let `S` be a scheme, let `(U ⊆ X, j : V ⟶ X)` be an elementary distinguished square of
algebraic spaces over `S` and set `T = |X| \ |U|`.  Let `j_!` and `Rj_*` be a left and a right
adjoint of derived restriction `(-)|_V : D(𝒪_X) ⥤ D(𝒪_V)`.

1. If `E` in `D(𝒪_X)` is supported on `T`, then (a) `E ⟶ Rj_*(E|_V)` and (b) `j_!(E|_V) ⟶ E`
   are isomorphisms.
2. If `F` in `D(𝒪_V)` is supported on `j^{-1}T`, then (a) `F ⟶ (j_!F)|_V`, (b)
   `(Rj_*F)|_V ⟶ F` and (c) `j_!F ⟶ Rj_*F` are isomorphisms.

The maps of (1)(a), (1)(b), (2)(a), (2)(b) are the units and counits of the two adjunctions,
and the map of (2)(c) is `AlgebraicGeometry.Space.supportedShriekToPushforward`. -/
@[stacks 08GG "all five clauses: for E in D(O_X) supported on T = |X| \\ |U| the unit
E ⟶ Rj_*(E|_V) and the counit j_!(E|_V) ⟶ E are isomorphisms, and for F in D(O_V) supported on
the preimage of T the unit F ⟶ (j_!F)|_V, the counit (Rj_*F)|_V ⟶ F and the comparison
j_!F ⟶ Rj_*F are isomorphisms. j_! and Rj_* are any left and right adjoints of derived
restriction, which pins them and their units and counits; the derived functor of
etaleModuleLowerShriek and a total right derived functor of j_* are such adjoints"]
theorem isIso_of_cohomologySupportedOn_edsEtale
    {shriekD RpushD : DerivedCategory (Modules.{u, u} B S hS (edsEtale B S hS hsq).1
        (edsEtale B S hS hsq).2) ⥤ DerivedCategory (Modules.{u, u} B S hS W.1 W.2)}
    (adjShriek : shriekD ⊣ (etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory)
    (adjPush : (etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory ⊣ RpushD) :
    (∀ E : DerivedCategory (Modules.{u, u} B S hS W.1 W.2),
      CohomologySupportedOn B S hS W.1 W.2 (edsComplementPoints B S hS Uo) E →
        IsIso (adjPush.unit.app E) ∧ IsIso (adjShriek.counit.app E)) ∧
    (∀ (F : DerivedCategory (Modules.{u, u} B S hS (edsEtale B S hS hsq).1
        (edsEtale B S hS hsq).2))
      (hF : CohomologySupportedOn B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2
        (edsEtalePreimageComplementPoints B S hS hsq) F),
        IsIso (adjShriek.unit.app F) ∧ IsIso (adjPush.counit.app F) ∧
          IsIso (supportedShriekToPushforward B S hS hsq adjShriek adjPush F
            (isIso_unit_derivedShriek_of_cohomologySupportedOn B S hS hsq adjShriek F hF))) :=
  ⟨fun E hE => ⟨isIso_unit_derivedRestrict_of_cohomologySupportedOn B S hS hsq adjPush E hE,
      isIso_counit_derivedRestrict_of_cohomologySupportedOn B S hS hsq adjShriek E hE⟩,
    fun F hF => ⟨isIso_unit_derivedShriek_of_cohomologySupportedOn B S hS hsq adjShriek F hF,
      isIso_counit_derivedPushforward_of_cohomologySupportedOn B S hS hsq adjPush F hF,
      isIso_supportedShriekToPushforward_of_supported B S hS hsq adjShriek adjPush F hF⟩⟩

end Square

end AlgebraicGeometry.Space

end
