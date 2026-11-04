module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinMapDeRham
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.AbelianCechClassPassage

/-!
# Stacks 0G85 for any number of equations

Let `π : X ⟶ S` be a morphism of schemes, let `f₁, …, f_c ∈ Γ(X, 𝒪_X)` be global functions —
**any number of them, `c = 0` included** — and let `i : Z ⟶ X` be a closed immersion cut out by
them.  [Stacks, Tag 0G85] says that the Gysin map

`γ^p_{f₁, …, f_c} : Ω^p_{Z/S} ⟶ ℋ ᶜ_Z(Ω^{p+c}_{X/S})`

of [Stacks, Tag 0G83] (`AlgebraicGeometry.Scheme.Hom.gysinMap`, which takes `f : Fin c → Γ(X, ⊤)`
for an arbitrary `c`) is compatible with the de Rham differentials on `Ω^•_{X/S}` and
`Ω^•_{Z/S}`.

`AlgebraicGeometry.Scheme.Hom.gysinMapCommutesWithDeRham` of
`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/GysinMapDeRham.lean` proves this only for a nonempty
family `Fin (c + 1)`, because its right-hand vertical arrow
`AlgebraicGeometry.Scheme.Hom.gysinTargetDeRhamMap` and the class-map naturality it rests on
(`Stacks.Perfect.SupportedEndoForgetDegreewise.gysinFormulaCommutesWithDeRham`) go through the
cokernel of the last differential of the extended alternating Čech complex, which does not exist
for an empty family.  This file proves the square for **every** `c`, by one argument that does not
split on `c`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.gysinMap_comm_deRham`: **[Stacks, Tag 0G85]** — for every
  `c : ℕ`, every `f : Fin c → Γ(X, ⊤)` cutting out `i` and every degree `p`, the square

  `i_*Ω^p_{Z/S} ⟶ i_*ℋ ᶜ_Z(Ω^{p+c}_{X/S})`,  `i_*Ω^{p+1}_{Z/S} ⟶ i_*ℋ ᶜ_Z(Ω^{p+c+1}_{X/S})`

  commutes.  It carries the `@[stacks 0G85]` attribute.
* `AlgebraicGeometry.Scheme.Hom.gysinFraction_comm_deRham`: steps (i)–(iii) of the source's proof
  for any number of equations — the fraction class of the Gysin numerator commutes with `d`.
* `AlgebraicGeometry.Scheme.Hom.pushforwardLocalCohomologyAbelianMap_eq_gysinTargetDeRhamMap`: at
  `c = d + 1` the right-hand vertical arrow used here *is* the base's
  `AlgebraicGeometry.Scheme.Hom.gysinTargetDeRhamMap`, by `rfl`.

## The square, arrow by arrow

* Horizontal arrows: the underlying abelian-sheaf morphisms of
  `AlgebraicGeometry.Scheme.Hom.gysinMap` in degrees `p` and `p + 1`.
* Left vertical arrow: the de Rham differential of `Z/S` pushed forward along `i`,
  `AlgebraicGeometry.Scheme.Hom.pushforwardDeRhamDifferentialAbHom`.
* Right vertical arrow: the action of `i_*ℋ ᶜ_Z` on the de Rham differential
  `d : Ω^{p+c}_{X/S} ⟶ Ω^{p+c+1}_{X/S}` of `X/S`, which is only `π⁻¹𝒪_S`-linear; it is
  `Stacks.Perfect.GysinAbelianSquare.pushforwardLocalCohomologyAbelianMap` at the zero locus of
  the equations and degree `c`, i.e. [Stacks, Tag 0G74] part (2) conjugating the abelian local
  cohomology functor — exactly the source's "the functor `ℋ ᶜ_Z` on `𝒪_X`-modules agrees with the
  one on abelian sheaves, hence `d` induces a map".  It is defined for every `c`.
* The Gysin map in degree `p + 1` lands in degree `(p + 1) + c`, the right vertical arrow in
  `p + c + 1`; the two are identified by the canonical `eqToHom` of `i_*ℋ ᶜ_Z(Ω^•_{X/S})` along
  `gysinAnyTargetDegree_eq`.

## Implementation notes

**Why no case split on `c`.**  The class map of [Stacks, Tag 0G7Q] has a spelling built without a
top Čech differential, `Stacks.Perfect.FractionClass.classMapToSupport`, and its naturality in a
merely additive morphism satisfying the localized Leibniz rule is
`Stacks.Perfect.AbelianCechClassPassage.classMapToSupport_comm_of_smul`, proved for every `c`.
The fraction class `AlgebraicGeometry.Scheme.Hom.formFractionClass` the Gysin map is built from is
that class map followed by the component of
`Stacks.Perfect.GysinLocalCohomology.supportCohomologySheafFunctorIso`
(`formFractionClass_eq_classMapToSupport`, from
`Stacks.Perfect.FractionClass.classMapToSupport_comp_supportCohomologyToPushforward` and
`Stacks.Perfect.SupportedEndoForgetDegreewise.supportCohomologySheafFunctorIso_hom_app_eq`), and
that component carries the two abelian actions of `i_*ℋ ᶜ_Z` into one another by construction
(`supportCohomologySheafFunctorIso_comp_pushforwardLocalCohomologyAbelianMap`).  The localized
Leibniz rule on the Gysin numerator is
`Stacks.Perfect.GysinFractionDeRham.sectionsHom_d_smul_gysinWedgeHom`, already stated for any
number of equations.  The passage from the Gysin formula to the Gysin map is the base file's: the
square is checked after precomposition with the epimorphism `formRestriction`.

**Carried hypotheses.**  `gysinMap_comm_deRham` carries `[IsClosedImmersion i]` and
`hcut : Stacks.Gysin.IsCutOutByEquations i f` — the hypotheses of `gysinMap` itself — and nothing
else; `c` is an arbitrary natural number.  No smoothness, regularity or finiteness hypothesis and
no proposition is assumed.

**Rearrangements at a variable category.**  Several steps cross definitionally equal but
differently spelled objects (`(p : ℤ) + (c : ℤ)` against `((p + c : ℕ) : ℤ)`, and
`supportCohomologySheaf` against `(supportCohomologySheafFunctor _ _).obj`), where `rw` refuses
to fire; they are done by `private` lemmas stated at a variable category and applied with
`exact`, as in `Stacks.Perfect.SupportedEndoForgetDegreewise`.

## References

* [Stacks Project, Tag 0G85](https://stacks.math.columbia.edu/tag/0G85)
* [Stacks Project, Tag 0G83](https://stacks.math.columbia.edu/tag/0G83)
* [Stacks Project, Tag 0G7Q](https://stacks.math.columbia.edu/tag/0G7Q)
* [Stacks Project, Lemma 20.34.8 (Tag 0G74)](https://stacks.math.columbia.edu/tag/0G74)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Perfect.AbelianFraction (abelianSheaf abHom)
open Stacks.Perfect.CechDerivedSupport (equationsClosedSet isClosed_equationsClosedSet)
open Stacks.Perfect.GysinAbelianSquare (pushforwardLocalCohomologyAbelianMap)

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Z S : Scheme.{u}}

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] isQuasicoherent_relativeDifferentialForms

/-- Cancelling an isomorphism appended and removed at the end of a composite, at abstract
categories. -/
private lemma cancel_tail_formal {C₀ D₀ : Type*} [Category* C₀] [Category* D₀] (W : D₀ ⥤ C₀)
    {A B C D : C₀} {P Q : D₀} (x : A ⟶ B) (y : B ⟶ C) (z : C ⟶ D) (t : D ⟶ W.obj Q)
    (e : P ≅ Q) :
    x ≫ y ≫ z ≫ t = ((x ≫ y) ≫ z ≫ t ≫ W.map e.inv) ≫ W.map e.hom := by
  simp only [Category.assoc, ← W.map_comp, Iso.inv_hom_id, W.map_id, Category.comp_id]

/-- Pasting a square onto the end of another, at an abstract category. -/
private lemma square_paste_formal {C₀ : Type*} [Category* C₀] {E F G F' G' M M' : C₀}
    (u : E ⟶ F) (a : F ⟶ M) (m : M ⟶ M') (w : E ⟶ G) (a' : G ⟶ M') (b : M ⟶ F')
    (l : F' ⟶ G') (b' : M' ⟶ G') (key : u ≫ a ≫ m = w ≫ a') (nat : b ≫ l = m ≫ b') :
    u ≫ (a ≫ b) ≫ l = w ≫ a' ≫ b' := by
  rw [Category.assoc, nat, ← Category.assoc a, ← Category.assoc, key, Category.assoc]

/-- Rewriting the first factor of a composite as a composite and reassociating, at an abstract
category. -/
private lemma comp_eq_of_assoc_formal {C₀ : Type*} [Category* C₀] {A B C D : C₀}
    (u : A ⟶ B) (a : B ⟶ C) (m : C ⟶ D) (rhs : A ⟶ D) (k : A ⟶ C) (h : u ≫ a ≫ m = rhs)
    (hk : k = u ≫ a) : k ≫ m = rhs := by
  rw [hk, Category.assoc, h]

/-- The chase assembling the square for the Gysin map from its precomposition with
restriction of forms, at an abstract category. -/
private lemma cancel_square_formal {C₀ : Type*} [Category* C₀] {A B C D B' C' : C₀}
    (r : A ⟶ B) (g : B ⟶ C) (l : C ⟶ D) (d : B ⟶ C') (y : C' ⟶ D) (k : A ⟶ C)
    (x : A ⟶ B') (r' : B' ⟶ C') (z : B' ⟶ D) {rhs : A ⟶ D} (h1 : r ≫ g = k)
    (h2 : k ≫ l = rhs) (h3 : r ≫ d = x ≫ r') (h4 : r' ≫ y = z) (h5 : x ≫ z = rhs) :
    r ≫ g ≫ l = r ≫ d ≫ y := by
  rw [← Category.assoc, h1, h2, ← Category.assoc, h3, Category.assoc, h4, h5]

/-- Splitting the last factor and reassociating, at an abstract category. -/
private lemma whisker_assoc_formal {C₀ : Type*} [Category* C₀] {A B C D : C₀}
    (x : A ⟶ B) (z : B ⟶ D) (a : B ⟶ C) (b : C ⟶ D) {a' : B ⟶ C} {n : A ⟶ C}
    (hz : z = a ≫ b) (ha : a = a') (hn : x ≫ a' = n) : x ≫ z = n ≫ b := by
  rw [hz, ha, ← Category.assoc, hn]

/-- **The fraction class of the Gysin map is the class map of [Stacks, Tag 0G7Q] in the support
spelling**, for any number of equations: `AlgebraicGeometry.Scheme.Hom.formFractionClass` is
`Stacks.Perfect.FractionClass.classMapToSupport` followed by the component of
`Stacks.Perfect.GysinLocalCohomology.supportCohomologySheafFunctorIso`, which moves the direct
image past the cohomology sheaf. -/
theorem formFractionClass_eq_classMapToSupport (π : X ⟶ S) {c : ℕ} (f : Fin c → Γ(X, ⊤))
    (q : ℤ) [(relativeDifferentialForms π q).IsQuasicoherent] :
    formFractionClass π f q =
      Stacks.Perfect.FractionClass.classMapToSupport f (relativeDifferentialForms π q)
          (isClosed_equationsClosedSet f) subset_rfl ≫
        (Stacks.Perfect.GysinLocalCohomology.supportCohomologySheafFunctorIso
          (isClosed_equationsClosedSet f) (c : ℤ)).hom.app (relativeDifferentialForms π q) := by
  rw [Stacks.Perfect.SupportedEndoForgetDegreewise.supportCohomologySheafFunctorIso_hom_app_eq]
  exact (Stacks.Perfect.FractionClass.classMapToSupport_comp_supportCohomologyToPushforward f
    (relativeDifferentialForms π q)).symm

/-- `formFractionClass_eq_classMapToSupport` read on the underlying abelian sheaves. -/
theorem abelianSheaf_map_formFractionClass (π : X ⟶ S) {c : ℕ} (f : Fin c → Γ(X, ⊤))
    (q : ℤ) [(relativeDifferentialForms π q).IsQuasicoherent] :
    (abelianSheaf X).map (formFractionClass π f q) =
      (abelianSheaf X).map
          (Stacks.Perfect.FractionClass.classMapToSupport f (relativeDifferentialForms π q)
            (isClosed_equationsClosedSet f) subset_rfl) ≫
        (abelianSheaf X).map
          ((Stacks.Perfect.GysinLocalCohomology.supportCohomologySheafFunctorIso
            (isClosed_equationsClosedSet f) (c : ℤ)).hom.app (relativeDifferentialForms π q)) :=
  (congrArg (abelianSheaf X).map (formFractionClass_eq_classMapToSupport π f q)).trans
    ((abelianSheaf X).map_comp _ _)

/-- **The two abelian actions of `i_*ℋ ⁿ_T` correspond under the comparison of the two places at
which the cohomology sheaf is taken.**  For a morphism `ψ` of the underlying abelian sheaves — not
required to be `𝒪_X`-linear — the component of
`Stacks.Perfect.GysinLocalCohomology.supportCohomologySheafFunctorIso` carries
`Stacks.Perfect.GysinAbelianSquare.supportCohomologySheafAbelianMap` to
`Stacks.Perfect.GysinAbelianSquare.pushforwardLocalCohomologyAbelianMap`.  This holds by
construction: the first action is the second conjugated by that component. -/
theorem supportCohomologySheafFunctorIso_comp_pushforwardLocalCohomologyAbelianMap
    {T : Set X} (hT : IsClosed T) (n : ℕ) {F G : X.Modules}
    (ψ : (abelianSheaf X).obj F ⟶ (abelianSheaf X).obj G) :
    (abelianSheaf X).map
          ((Stacks.Perfect.GysinLocalCohomology.supportCohomologySheafFunctorIso hT
            (n : ℤ)).hom.app F) ≫
        pushforwardLocalCohomologyAbelianMap hT n ψ =
      Stacks.Perfect.GysinAbelianSquare.supportCohomologySheafAbelianMap hT n ψ ≫
        (abelianSheaf X).map
          ((Stacks.Perfect.GysinLocalCohomology.supportCohomologySheafFunctorIso hT
            (n : ℤ)).hom.app G) := by
  simp only [Stacks.Perfect.GysinAbelianSquare.supportCohomologySheafAbelianMap,
    Stacks.Perfect.GysinAbelianSquare.supportCohomologySheafForgetIso,
    pushforwardLocalCohomologyAbelianMap, Iso.trans_hom, Iso.trans_inv, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv, Functor.whiskerRight_app]
  exact cancel_tail_formal (abelianSheaf X) _ _ _ _
    ((Stacks.Perfect.GysinLocalCohomology.supportCohomologySheafFunctorIso hT (n : ℤ)).app G)

/-- **Steps (i)–(iii) of the proof of [Stacks, Tag 0G85], for any number of equations.**  The
fraction class of `ω̃ ∧ d f₁ ∧ ⋯ ∧ d f_c`, followed by the action of `i_*ℋ ᶜ_Z` on the de Rham
differential, is the fraction class of `d ω̃ ∧ d f₁ ∧ ⋯ ∧ d f_c`.

This is `Stacks.Perfect.AbelianCechClassPassage.classMapToSupport_comm_of_smul` — the localized
Leibniz rule for the class map, proved for every `c` — fed the Gysin numerator through
`Stacks.Perfect.GysinFractionDeRham.sectionsHom_d_smul_gysinWedgeHom`, and carried to the Gysin
map's spelling by `formFractionClass_eq_classMapToSupport` and
`supportCohomologySheafFunctorIso_comp_pushforwardLocalCohomologyAbelianMap`. -/
theorem gysinFraction_comm_deRham (π : X ⟶ S) {c : ℕ} (f : Fin c → Γ(X, ⊤)) (p : ℕ) :
    abHom (Stacks.Perfect.GysinFractionDeRham.gysinWedgePresheafHom π f p) ≫
        (abelianSheaf X).map (formFractionClass π f ((p + c : ℕ) : ℤ)) ≫
          pushforwardLocalCohomologyAbelianMap (isClosed_equationsClosedSet f) c
            (deRhamDifferentialAbHom π (p + c)) =
      abHom (Stacks.Perfect.GysinFractionDeRham.gysinNumeratorPresheafHom π f p) ≫
        (abelianSheaf X).map (formFractionClass π f ((p + c + 1 : ℕ) : ℤ)) := by
  have key := Stacks.Perfect.AbelianCechClassPassage.classMapToSupport_comm_of_smul f
    (deRhamDifferentialPresheafHom π (p + c))
    (Stacks.Perfect.GysinFractionDeRham.gysinWedgePresheafHom π f p)
    (Stacks.Perfect.GysinFractionDeRham.gysinNumeratorPresheafHom π f p)
    (fun V v y hv =>
      Stacks.Perfect.GysinFractionDeRham.sectionsHom_d_smul_gysinWedgeHom π f p V v hv y)
    (isClosed_equationsClosedSet f) subset_rfl
  rw [abelianSheaf_map_formFractionClass, abelianSheaf_map_formFractionClass]
  exact square_paste_formal _ _ _ _ _ _ _ _ key
    (supportCohomologySheafFunctorIso_comp_pushforwardLocalCohomologyAbelianMap
      (isClosed_equationsClosedSet f) c (deRhamDifferentialAbHom π (p + c)))

/-- The Gysin formula followed by a degree transport of its target is the wedge factor, the
corresponding transport of the de Rham term, and the fraction class in the transported degree. -/
theorem gysinFormulaHom_comp_eqToHom (π : X ⟶ S) {c : ℕ} (f : Fin c → Γ(X, ⊤)) {m n : ℤ}
    (h : m + (c : ℤ) = n) [(relativeDifferentialForms π (m + (c : ℤ))).IsQuasicoherent]
    [(relativeDifferentialForms π n).IsQuasicoherent] :
    gysinFormulaHom π f m ≫
        eqToHom (congrArg
          (fun k : ℤ => pushforwardLocalCohomology f (relativeDifferentialForms π k))
          h) =
      (gysinWedgeHom π f m ≫ eqToHom (congrArg (relativeDifferentialForms π) h)) ≫
        formFractionClass π f n := by
  subst h
  simp only [eqToHom_refl, Category.comp_id]
  rfl

/-- The degree equality `(p + 1) + c = p + c + 1` relating the targets of the two horizontal
arrows of the square of [Stacks, Tag 0G85], for an arbitrary number `c` of equations. -/
theorem gysinAnyTargetDegree_eq (c p : ℕ) :
    ((p + 1 : ℕ) : ℤ) + (c : ℤ) = ((p + c + 1 : ℕ) : ℤ) := by
  push_cast; ring

/-- The wedge factor in degree `p + 1` followed by the degree transport, read on underlying
abelian presheaves, is the wedge factor followed by
`AlgebraicGeometry.Scheme.Hom.deRhamReindexPresheafHom`. -/
theorem mapPresheaf_gysinWedgeHom_comp_eqToHom_eq (π : X ⟶ S) {c : ℕ} (f : Fin c → Γ(X, ⊤))
    (p : ℕ) :
    Scheme.Modules.Hom.mapPresheaf (gysinWedgeHom π f ((p + 1 : ℕ) : ℤ) ≫
        eqToHom (congrArg (relativeDifferentialForms π) (gysinAnyTargetDegree_eq c p))) =
      Scheme.Modules.Hom.mapPresheaf (gysinWedgeHom π f ((p + 1 : ℕ) : ℤ)) ≫
        deRhamReindexPresheafHom π (show p + 1 + c = p + c + 1 by omega) :=
  (mapPresheaf_comp _ _).trans
    (whisker_eq _ (deRhamReindexPresheafHom_eq_mapPresheaf π _).symm)

/-- `mapPresheaf_gysinWedgeHom_comp_eqToHom_eq` read on the underlying abelian sheaves. -/
theorem abelianSheaf_map_gysinWedgeHom_comp_eqToHom_eq (π : X ⟶ S) {c : ℕ}
    (f : Fin c → Γ(X, ⊤)) (p : ℕ) :
    (abelianSheaf X).map (gysinWedgeHom π f ((p + 1 : ℕ) : ℤ) ≫
        eqToHom (congrArg (relativeDifferentialForms π) (gysinAnyTargetDegree_eq c p))) =
      abHom (Scheme.Modules.Hom.mapPresheaf (gysinWedgeHom π f ((p + 1 : ℕ) : ℤ)) ≫
        deRhamReindexPresheafHom π (show p + 1 + c = p + c + 1 by omega)) :=
  (Stacks.Perfect.AbelianFraction.abelianSheaf_map _).trans
    (congrArg abHom (mapPresheaf_gysinWedgeHom_comp_eqToHom_eq π f p))

/-- The de Rham differential followed by the reindexed wedge factor is the Gysin numerator
`Stacks.Perfect.GysinFractionDeRham.gysinNumeratorPresheafHom`, by definition. -/
theorem abHom_gysinNumeratorPresheafHom_eq (π : X ⟶ S) {c : ℕ} (f : Fin c → Γ(X, ⊤))
    (p : ℕ) :
    deRhamDifferentialAbHom π p ≫
        abHom (Scheme.Modules.Hom.mapPresheaf (gysinWedgeHom π f ((p + 1 : ℕ) : ℤ)) ≫
          deRhamReindexPresheafHom π (show p + 1 + c = p + c + 1 by omega)) =
      abHom (Stacks.Perfect.GysinFractionDeRham.gysinNumeratorPresheafHom π f p) := rfl

/-- The reindexed Gysin formula in degree `p + 1`, read on the underlying abelian sheaves, split
into the reindexed wedge factor and the fraction class. -/
theorem abelianSheaf_map_gysinFormulaHom_comp_eqToHom (π : X ⟶ S) {c : ℕ}
    (f : Fin c → Γ(X, ⊤)) (p : ℕ) :
    (abelianSheaf X).map (gysinFormulaHom π f ((p + 1 : ℕ) : ℤ) ≫
        eqToHom (congrArg
          (fun k : ℤ => pushforwardLocalCohomology f (relativeDifferentialForms π k))
          (gysinAnyTargetDegree_eq c p))) =
      (abelianSheaf X).map (gysinWedgeHom π f ((p + 1 : ℕ) : ℤ) ≫
          eqToHom (congrArg (relativeDifferentialForms π) (gysinAnyTargetDegree_eq c p))) ≫
        (abelianSheaf X).map (formFractionClass π f ((p + c + 1 : ℕ) : ℤ)) :=
  (congrArg (abelianSheaf X).map
      (gysinFormulaHom_comp_eqToHom π f (gysinAnyTargetDegree_eq c p))).trans
    ((abelianSheaf X).map_comp _ _)

/-- **The square of [Stacks, Tag 0G85] for the Gysin formula, for any number of equations**: the
Gysin formula followed by the action of `i_*ℋ ᶜ_Z` on `d` is the fraction class of the Gysin
numerator in degree `p + 1`. -/
theorem abelianSheaf_map_gysinFormulaHom_comm (π : X ⟶ S) {c : ℕ} (f : Fin c → Γ(X, ⊤))
    (p : ℕ) :
    (abelianSheaf X).map (gysinFormulaHom π f (p : ℤ)) ≫
        pushforwardLocalCohomologyAbelianMap (isClosed_equationsClosedSet f) c
          (deRhamDifferentialAbHom π (p + c)) =
      abHom (Stacks.Perfect.GysinFractionDeRham.gysinNumeratorPresheafHom π f p) ≫
        (abelianSheaf X).map (formFractionClass π f ((p + c + 1 : ℕ) : ℤ)) :=
  comp_eq_of_assoc_formal _ _ _ _ _ (gysinFraction_comm_deRham π f p)
    ((abelianSheaf X).map_comp _ _)

/-- **Stacks Project, Tag 0G85.**  The Gysin map `γ^p_{f₁, …, f_c}` of [Stacks, Tag 0G83] is
compatible with the de Rham differentials on `Ω^•_{X/S}` and `Ω^•_{Z/S}`, for **every** number
`c ≥ 0` of equations: the square

`i_*Ω^p_{Z/S} ⟶ i_*ℋ ᶜ_Z(Ω^{p+c}_{X/S})`,  `i_*Ω^{p+1}_{Z/S} ⟶ i_*ℋ ᶜ_Z(Ω^{p+c+1}_{X/S})`

commutes, whose horizontal arrows are `AlgebraicGeometry.Scheme.Hom.gysinMap` in degrees `p` and
`p + 1` (read on underlying abelian sheaves, the second followed by the canonical identification of
the degrees `(p + 1) + c = p + c + 1`), whose left vertical arrow is the de Rham differential of
`Z/S` pushed forward along `i`, and whose right vertical arrow is the action of `i_*ℋ ᶜ_Z` on the
de Rham differential of `X/S` given by [Stacks, Tag 0G74] part (2).

The square is checked after precomposition with the epimorphism of restriction of forms to `Z`,
where the Gysin map becomes the Gysin formula, and there it is
`abelianSheaf_map_gysinFormulaHom_comm`.
The hypotheses are exactly those of `gysinMap`: `i` a closed immersion cut out by
`f : Fin c → Γ(X, ⊤)`, with `c` arbitrary — `c = 0` included. -/
@[stacks 0G85]
theorem gysinMap_comm_deRham (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S) {c : ℕ}
    (f : Fin c → Γ(X, ⊤)) (p : ℕ) (hcut : Stacks.Gysin.IsCutOutByEquations i f) :
    (abelianSheaf X).map (gysinMap i π f p hcut) ≫
        pushforwardLocalCohomologyAbelianMap (isClosed_equationsClosedSet f) c
          (deRhamDifferentialAbHom π (p + c)) =
      pushforwardDeRhamDifferentialAbHom i π p ≫
        (abelianSheaf X).map (gysinMap i π f (p + 1) hcut ≫
          eqToHom (congrArg
            (fun k : ℤ => pushforwardLocalCohomology f (relativeDifferentialForms π k))
            (gysinAnyTargetDegree_eq c p))) := by
  have hepi := epi_abelianSheaf_formRestriction i π p
  refine (cancel_epi ((abelianSheaf X).map (formRestriction i π (p : ℤ)))).mp ?_
  have h1 : (abelianSheaf X).map (formRestriction i π (p : ℤ)) ≫
      (abelianSheaf X).map (gysinMap i π f p hcut) =
        (abelianSheaf X).map (gysinFormulaHom π f (p : ℤ)) :=
    ((abelianSheaf X).map_comp _ _).symm.trans
      (congrArg (abelianSheaf X).map (formRestriction_comp_gysinMap i π f p hcut))
  have h3 : (abelianSheaf X).map (formRestriction i π ((p + 1 : ℕ) : ℤ)) ≫
      (abelianSheaf X).map (gysinMap i π f (p + 1) hcut ≫
          eqToHom (congrArg
            (fun k : ℤ => pushforwardLocalCohomology f (relativeDifferentialForms π k))
            (gysinAnyTargetDegree_eq c p))) =
        (abelianSheaf X).map (gysinFormulaHom π f ((p + 1 : ℕ) : ℤ) ≫
          eqToHom (congrArg
            (fun k : ℤ => pushforwardLocalCohomology f (relativeDifferentialForms π k))
            (gysinAnyTargetDegree_eq c p))) :=
    ((abelianSheaf X).map_comp _ _).symm.trans (congrArg (abelianSheaf X).map (by
      rw [← Category.assoc, formRestriction_comp_gysinMap]))
  exact cancel_square_formal _ _ _ _ _ _ _ _ _ h1 (abelianSheaf_map_gysinFormulaHom_comm π f p)
    (formRestriction_comm_deRhamDifferentialAbHom i π p) h3
    (whisker_assoc_formal _ _ _ _ (abelianSheaf_map_gysinFormulaHom_comp_eqToHom π f p)
      (abelianSheaf_map_gysinWedgeHom_comp_eqToHom_eq π f p)
      (abHom_gysinNumeratorPresheafHom_eq π f p))

/-- **At a nonempty family the right-hand vertical arrow is the base's.**  For `c = d + 1` the
action of `i_*ℋ ᶜ_Z` on the de Rham differential used in `gysinMap_comm_deRham` is
`AlgebraicGeometry.Scheme.Hom.gysinTargetDeRhamMap`, the right-hand vertical arrow of
`AlgebraicGeometry.Scheme.Hom.GysinMapCommutesWithDeRham`, by definition. -/
theorem pushforwardLocalCohomologyAbelianMap_eq_gysinTargetDeRhamMap (π : X ⟶ S) {d : ℕ}
    (f : Fin (d + 1) → Γ(X, ⊤)) (q : ℕ) :
    pushforwardLocalCohomologyAbelianMap (isClosed_equationsClosedSet f) (d + 1)
        (deRhamDifferentialAbHom π q) =
      gysinTargetDeRhamMap π f q := rfl

end AlgebraicGeometry.Scheme.Hom

end
