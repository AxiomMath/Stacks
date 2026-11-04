module

public import StacksCore.Tactic.StacksAttribute
public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.AssociatedPointInductionComparison
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.ComparisonAdicLimitExact
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.ComparisonPresentation
public import StacksFrontier.AlgebraicGeometry.Modules.LocalSectionHom

/-!
# The middle comparison of a short exact sequence

Let `I ⊆ 𝔞` be ideals of a Noetherian ring `A`, let `U = Spec(A) ∖ V(𝔞)` and let
`0 → F' → F → F'' → 0` be a short exact sequence of coherent modules on `U`. If the comparison
maps of `Stacks.Algebraization.comparisonMap` for `F'` and `F''` are isomorphisms, so is the one
for `F`.

Injectivity is a diagram chase,
`Stacks.Algebraization.injective_comparisonMap_middle_of_shortExact`. A formal section `ŝ` of `F`
has an image in the formal sections of `F''`, which comes from a genuine section `t` of `F''` on a
neighbourhood `V` of the formal locus. Writing `t` as a morphism out of a power `K ⁿ · 𝒪_U` of an
ideal sheaf missing `V`, and presenting that power by a finite free module mapping also to `F`, one
obtains finitely many generators `cᵢ : 𝒪_U ⟶ 𝒪_U` of that power together with lifts `mᵢ : 𝒪_U ⟶ F`.
Each `cᵢ · ŝ - (mᵢ)_*` dies in the formal sections of `F''`, hence comes from a formal section of
`F'`, which on a smaller neighbourhood is a genuine section; the corrected sections `uᵢ` of `F`
then satisfy every relation among the generators, because the comparison for `F` is injective, and
so descend to a single section `s` of `F` whose comparison is `ŝ`.

## Main results

* `Stacks.Algebraization.isIso_comparisonMap_middle_of_ends` — **Stacks 0H48, the middle
  comparison.**
* `Stacks.Algebraization.middleComparisonOfShortExact` — the same statement in the packaged form
  `Stacks.Algebraization.MiddleComparisonOfShortExact`.

## Implementation notes

A formal section of `F` is an element of a limit of abelian groups, while the argument needs it as
a morphism `𝒪_U ⟶ lim_n F / Iⁿ F` of modules, so that it can be multiplied by the generators `cᵢ`
and corrected by the `mᵢ`. `Stacks.Algebraization.formalSectionHom` is that dictionary; it is a
bijection, and the middle exactness of the limits of the quotient towers is read through it from
`Stacks.Algebraization.exists_limMap_formalSectionsMap_eq`.

`AlgebraicGeometry.Scheme.Modules` is a `def`, and the two presentations of the category of
modules carry separately declared `Category` and `Preadditive` instances, so `rw` fails on goals
mixing the two spellings: its motive is built at `implicit` transparency. The cancellation steps
below are therefore written in term mode, as `calc` and `Category.assoc`/`congrArg` chains, and
the level of a formal section is recorded by `Stacks.Algebraization.formalSectionAt`, whose
ascribed type is the group of sections of the quotient rather than the value of the diagram of
formal sections.

## References

* [Stacks Project, Tag 0H48](https://stacks.math.columbia.edu/tag/0H48)
* [Stacks Project, Tag 0EG2](https://stacks.math.columbia.edu/tag/0EG2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Ample (unitModule)
open Stacks.AlgebraicGeometry.LocalSection
open Stacks.AlgebraicGeometry.IdealPowerHomColimit

universe u

namespace Stacks.Algebraization

open Stacks.LocalCohomology

/-! ### Global sections and morphisms out of the structure sheaf -/

/-- The global section attached to a morphism out of the structure sheaf is the image of the
unit function. -/
private theorem globalSectionOfHom_apply {X : Scheme.{u}} (M : X.Modules)
    (u : unitModule X ⟶ M) :
    globalSectionOfHom M u = Scheme.Modules.Hom.app u ⊤ (1 : Γ(X, (⊤ : X.Opens))) := rfl

/-- A global section of a module, read as a morphism from the structure sheaf, with the
presentation of the category pinned to `AlgebraicGeometry.Scheme.Modules`. -/
private abbrev homOfSection {X : Scheme.{u}} (M : X.Modules) (x : Γ(M, (⊤ : X.Opens))) :
    unitModule X ⟶ M :=
  homOfGlobalSection M x

/-- The global section attached to the zero morphism out of the structure sheaf vanishes. -/
private theorem globalSectionOfHom_zero_hom {X : Scheme.{u}} (M : X.Modules) :
    globalSectionOfHom M (0 : unitModule X ⟶ M) = 0 := by
  show Scheme.Modules.Hom.app (0 : unitModule X ⟶ M) ⊤ (1 : Γ(X, (⊤ : X.Opens))) = 0
  rw [Scheme.Modules.Hom.zero_app]
  rfl

/-- A morphism out of the structure sheaf carries the unit function of an open to the restriction
of its global section. -/
private theorem unit_hom_app_one {X : Scheme.{u}} (M : X.Modules)
    (u : unitModule X ⟶ M) (V : X.Opens) :
    u.val.app (op V) (1 : Γ(X, V)) =
      M.presheaf.map (homOfLE (le_top (a := V))).op (globalSectionOfHom M u) := by
  have hn := ConcreteCategory.congr_hom
    ((Scheme.Modules.Hom.mapPresheaf (X := X) u).naturality
      (homOfLE (le_top (a := V))).op) (1 : Γ(X, (⊤ : X.Opens)))
  change u.val.app (op V)
      (X.presheaf.map (homOfLE (le_top (a := V))).op (1 : Γ(X, (⊤ : X.Opens)))) =
    M.presheaf.map (homOfLE (le_top (a := V))).op
      (u.val.app (op (⊤ : X.Opens)) (1 : Γ(X, (⊤ : X.Opens)))) at hn
  rwa [map_one] at hn

/-- Composing the morphism of a global section with a morphism of modules gives the morphism of
the image of that section. -/
private theorem homOfGlobalSection_comp_hom {X : Scheme.{u}} (M N : X.Modules)
    (x : Γ(M, (⊤ : X.Opens))) (φ : M ⟶ N) :
    homOfSection M x ≫ φ = homOfSection N (Scheme.Modules.Hom.app φ ⊤ x) :=
  (homOfGlobalSection_globalSectionOfHom N (homOfSection M x ≫ φ)).symm.trans
    (congrArg (homOfSection N)
      ((globalSectionOfHom_comp M (homOfSection M x) φ).trans
        (congrArg (fun y : Γ(M, (⊤ : X.Opens)) => Scheme.Modules.Hom.app φ ⊤ y)
          (globalSectionOfHom_homOfGlobalSection M x))))

/-- The restriction to an open `V` of the morphism of a global section is the morphism of the
section restricted to `V`. -/
private theorem localSectionHom_homOfSection {X : Scheme.{u}} (V : X.Opens)
    (M : X.Modules) (x : Γ(M, (⊤ : X.Opens))) :
    (Scheme.Modules.restrictFunctor V.ι).map (homOfSection M x) =
      localSectionHom V M (M.presheaf.map (homOfLE (le_top (a := V))).op x) :=
  (restrict_unit_hom_eq_localSectionHom V (homOfSection M x)).trans
    (congrArg (localSectionHom V M)
      ((unit_hom_app_one M (homOfSection M x) V).trans
        (congrArg (fun y : Γ(M, (⊤ : X.Opens)) =>
            M.presheaf.map (homOfLE (le_top (a := V))).op y)
          (globalSectionOfHom_homOfGlobalSection M x))))

/-! ### The limit of the tower of adic quotients -/

/-- The inverse limit of the tower of ideal-power quotients of a module, with its category
pinned to `AlgebraicGeometry.Scheme.Modules`. -/
private abbrev adicLimitObj {X : Scheme.{u}} (J : X.IdealSheafData) (F : X.Modules) :
    X.Modules :=
  limit (C := X.Modules) (adicQuotientSystem J F)

/-- The map of the inverse limits of the towers of ideal-power quotients induced by a morphism of
modules. -/
private abbrev adicLimitMap {X : Scheme.{u}} (J : X.IdealSheafData) {F G : X.Modules}
    (f : F ⟶ G) : adicLimitObj J F ⟶ adicLimitObj J G :=
  limMap (C := X.Modules) (adicQuotientSystemMap J f)

/-- The canonical morphism from a module to the limit of its tower of ideal-power quotients. -/
private def adicLimitLift {X : Scheme.{u}} (J : X.IdealSheafData) (F : X.Modules) :
    F ⟶ adicLimitObj J F :=
  limit.lift (adicQuotientSystem J F) (adicQuotientCone J F)

/-- The canonical morphism to the limit of the tower of ideal-power quotients, read at one level,
is the quotient projection. -/
private theorem adicLimitLift_π {X : Scheme.{u}} (J : X.IdealSheafData) (F : X.Modules)
    (n : ℕᵒᵖ) :
    adicLimitLift J F ≫ limit.π (adicQuotientSystem J F) n = adicProj J F n :=
  limit.lift_π (adicQuotientCone J F) n

/-- Reduction modulo `Iⁿ` commutes with a morphism of modules. -/
private theorem adicProj_comp_adicQuotientSystemMap_app {X : Scheme.{u}} (J : X.IdealSheafData)
    {F G : X.Modules} (f : F ⟶ G) (n : ℕᵒᵖ) :
    adicProj J F n ≫ (adicQuotientSystemMap J f).app n = f ≫ adicProj J G n :=
  idealPowerQuotientMap_π J J n.unop n.unop le_rfl f

/-! ### Formal sections as morphisms out of the structure sheaf -/

/-- The global section of `F / Iⁿ F` on `U` that a formal section records at level `n`. -/
private def formalSectionAt (A : Type u) [CommRing A] (I a : Ideal A)
    (F : (complementZeroLocus A a : Scheme).Modules)
    (w : ToType (limit (formalSections A I a F))) (n : ℕᵒᵖ) :
    Γ((quotientSystemNearVanishing A I a F).obj n,
      (⊤ : (complementZeroLocus A a : Scheme).Opens)) :=
  ConcreteCategory.hom (limit.π (formalSections A I a F) n) w

/-- The levels of a formal section are compatible with the transitions of the quotient tower. -/
private theorem formalSectionAt_map (A : Type u) [CommRing A] (I a : Ideal A)
    (F : (complementZeroLocus A a : Scheme).Modules)
    (w : ToType (limit (formalSections A I a F))) {m n : ℕᵒᵖ} (g : m ⟶ n) :
    Scheme.Modules.Hom.app ((quotientSystemNearVanishing A I a F).map g) ⊤
        (formalSectionAt A I a F w m) =
      formalSectionAt A I a F w n := by
  have hw := ConcreteCategory.congr_hom (limit.w (formalSections A I a F) g) w
  simp only [ConcreteCategory.comp_apply] at hw
  exact hw

/-- A formal section is determined by its levels. -/
private theorem formalSectionAt_ext (A : Type u) [CommRing A] (I a : Ideal A)
    (F : (complementZeroLocus A a : Scheme).Modules)
    (w w' : ToType (limit (formalSections A I a F)))
    (h : ∀ n, formalSectionAt A I a F w n = formalSectionAt A I a F w' n) : w = w' :=
  Concrete.limit_ext (formalSections A I a F) w w' h

/-- Every level of the zero formal section vanishes. -/
private theorem formalSectionAt_zero (A : Type u) [CommRing A] (I a : Ideal A)
    (F : (complementZeroLocus A a : Scheme).Modules) (n : ℕᵒᵖ) :
    formalSectionAt A I a F 0 n = 0 :=
  map_zero (ConcreteCategory.hom (limit.π (formalSections A I a F) n))

/-- The levels of the image of a formal section under a morphism of modules. -/
private theorem formalSectionAt_limMap (A : Type u) [CommRing A] (I a : Ideal A)
    {F G : (complementZeroLocus A a : Scheme).Modules} (f : F ⟶ G)
    (w : ToType (limit (formalSections A I a F))) (n : ℕᵒᵖ) :
    formalSectionAt A I a G
        (ConcreteCategory.hom (limMap (formalSectionsMap A I a f)) w) n =
      Scheme.Modules.Hom.app
        ((adicQuotientSystemMap (idealSheafNearVanishing A I a) f).app n) ⊤
        (formalSectionAt A I a F w n) := by
  have hw := ConcreteCategory.congr_hom (limMap_π (formalSectionsMap A I a f) n) w
  simp only [ConcreteCategory.comp_apply] at hw
  exact hw

/-- The cone over the tower of quotients `F / Iⁿ F` with vertex the structure sheaf determined by
a formal section. -/
private def formalSectionCone (A : Type u) [CommRing A] (I a : Ideal A)
    (F : (complementZeroLocus A a : Scheme).Modules)
    (w : ToType (limit (formalSections A I a F))) :
    Cone (quotientSystemNearVanishing A I a F) where
  pt := unitModule (complementZeroLocus A a : Scheme)
  π :=
  { app := fun n => homOfSection ((quotientSystemNearVanishing A I a F).obj n)
      (formalSectionAt A I a F w n)
    naturality := fun _m n g => (Category.id_comp _).trans
      ((congrArg (homOfSection ((quotientSystemNearVanishing A I a F).obj n))
          (formalSectionAt_map A I a F w g).symm).trans
        (homOfGlobalSection_comp_hom _ _ _ _).symm) }

/-- A formal section of `F` along `U ∩ V(I)`, read as a morphism from the structure sheaf of `U`
to the limit of the tower of quotients `F / Iⁿ F`. -/
private def formalSectionHom (A : Type u) [CommRing A] (I a : Ideal A)
    (F : (complementZeroLocus A a : Scheme).Modules)
    (w : ToType (limit (formalSections A I a F))) :
    unitModule (complementZeroLocus A a : Scheme) ⟶
      adicLimitObj (idealSheafNearVanishing A I a) F :=
  limit.lift (quotientSystemNearVanishing A I a F) (formalSectionCone A I a F w)

/-- The morphism of a formal section, read at one level of the tower, is the morphism of that
level's global section. -/
private theorem formalSectionHom_π (A : Type u) [CommRing A] (I a : Ideal A)
    (F : (complementZeroLocus A a : Scheme).Modules)
    (w : ToType (limit (formalSections A I a F))) (n : ℕᵒᵖ) :
    formalSectionHom A I a F w ≫ limit.π (quotientSystemNearVanishing A I a F) n =
      homOfSection ((quotientSystemNearVanishing A I a F).obj n)
        (formalSectionAt A I a F w n) :=
  limit.lift_π (formalSectionCone A I a F w) n

/-- The global section of the morphism of a formal section at one level is that level. -/
private theorem globalSectionOfHom_formalSectionHom_π (A : Type u) [CommRing A] (I a : Ideal A)
    (F : (complementZeroLocus A a : Scheme).Modules)
    (w : ToType (limit (formalSections A I a F))) (n : ℕᵒᵖ) :
    globalSectionOfHom ((quotientSystemNearVanishing A I a F).obj n)
        (formalSectionHom A I a F w ≫ limit.π (quotientSystemNearVanishing A I a F) n) =
      formalSectionAt A I a F w n :=
  (congrArg (globalSectionOfHom ((quotientSystemNearVanishing A I a F).obj n))
      (formalSectionHom_π A I a F w n)).trans
    (globalSectionOfHom_homOfGlobalSection _ _)

/-- Distinct formal sections give distinct morphisms out of the structure sheaf. -/
private theorem formalSectionHom_injective (A : Type u) [CommRing A] (I a : Ideal A)
    (F : (complementZeroLocus A a : Scheme).Modules) :
    Function.Injective (formalSectionHom A I a F) := fun w w' h =>
  formalSectionAt_ext A I a F w w' fun n =>
    (globalSectionOfHom_formalSectionHom_π A I a F w n).symm.trans
      ((congrArg (fun k => globalSectionOfHom
          ((quotientSystemNearVanishing A I a F).obj n)
          (k ≫ limit.π (quotientSystemNearVanishing A I a F) n)) h).trans
        (globalSectionOfHom_formalSectionHom_π A I a F w' n))

/-- The morphism of the zero formal section vanishes after restriction to a neighbourhood of the
formal locus. -/
private theorem restrict_formalSectionHom_zero (A : Type u) [CommRing A] (I a : Ideal A)
    (F : (complementZeroLocus A a : Scheme).Modules) (V : OpensNearVanishing A I a) (n : ℕᵒᵖ) :
    (Scheme.Modules.restrictFunctor V.openSet.ι).map
        (formalSectionHom A I a F 0 ≫ limit.π (quotientSystemNearVanishing A I a F) n) = 0 :=
  ((congrArg (fun z => (Scheme.Modules.restrictFunctor V.openSet.ι).map z)
        (formalSectionHom_π A I a F 0 n)).trans
      (localSectionHom_homOfSection V.openSet _ _)).trans
    ((congrArg (localSectionHom V.openSet ((quotientSystemNearVanishing A I a F).obj n))
        ((congrArg (fun y => ((quotientSystemNearVanishing A I a F).obj n).presheaf.map
            (homOfLE (le_top (a := V.openSet))).op y)
          (formalSectionAt_zero A I a F n)).trans (map_zero _))).trans
      (localSectionHom_zero V.openSet _))

/-- The dictionary between formal sections and morphisms out of the structure sheaf is natural in
the module, read at one level of the tower. -/
private theorem formalSectionHom_natural_π (A : Type u) [CommRing A] (I a : Ideal A)
    {F G : (complementZeroLocus A a : Scheme).Modules} (f : F ⟶ G)
    (w : ToType (limit (formalSections A I a F))) (n : ℕᵒᵖ) :
    formalSectionHom A I a G (ConcreteCategory.hom (limMap (formalSectionsMap A I a f)) w) ≫
        limit.π (quotientSystemNearVanishing A I a G) n =
      formalSectionHom A I a F w ≫ limit.π (quotientSystemNearVanishing A I a F) n ≫
        (adicQuotientSystemMap (idealSheafNearVanishing A I a) f).app n :=
  calc formalSectionHom A I a G
            (ConcreteCategory.hom (limMap (formalSectionsMap A I a f)) w) ≫
          limit.π (quotientSystemNearVanishing A I a G) n
        = homOfSection ((quotientSystemNearVanishing A I a G).obj n)
            (Scheme.Modules.Hom.app
              ((adicQuotientSystemMap (idealSheafNearVanishing A I a) f).app n) ⊤
              (formalSectionAt A I a F w n)) :=
          (formalSectionHom_π A I a G _ n).trans
            (congrArg (homOfSection ((quotientSystemNearVanishing A I a G).obj n))
              (formalSectionAt_limMap A I a f w n))
      _ = homOfSection ((quotientSystemNearVanishing A I a F).obj n)
            (formalSectionAt A I a F w n) ≫
            (adicQuotientSystemMap (idealSheafNearVanishing A I a) f).app n :=
          (homOfGlobalSection_comp_hom _ _ _ _).symm
      _ = (formalSectionHom A I a F w ≫
            limit.π (quotientSystemNearVanishing A I a F) n) ≫
            (adicQuotientSystemMap (idealSheafNearVanishing A I a) f).app n :=
          congrArg (fun k => k ≫
            (adicQuotientSystemMap (idealSheafNearVanishing A I a) f).app n)
            (formalSectionHom_π A I a F w n).symm
      _ = _ := Category.assoc _ _ _

/-- The dictionary between formal sections and morphisms out of the structure sheaf is natural in
the module. -/
private theorem formalSectionHom_natural (A : Type u) [CommRing A] (I a : Ideal A)
    {F G : (complementZeroLocus A a : Scheme).Modules} (f : F ⟶ G)
    (w : ToType (limit (formalSections A I a F))) :
    formalSectionHom A I a G (ConcreteCategory.hom (limMap (formalSectionsMap A I a f)) w) =
      formalSectionHom A I a F w ≫ adicLimitMap (idealSheafNearVanishing A I a) f :=
  limit.hom_ext (F := quotientSystemNearVanishing A I a G) fun n =>
    (formalSectionHom_natural_π A I a f w n).trans
      ((congrArg (fun k => formalSectionHom A I a F w ≫ k)
        (limMap_π (adicQuotientSystemMap (idealSheafNearVanishing A I a) f) n)).symm.trans
        (Category.assoc _ _ _).symm)

/-- Every morphism from the structure sheaf of `U` to the limit of the tower of quotients
`F / Iⁿ F` comes from a formal section. -/
private theorem exists_formalSection_of_hom (A : Type u) [CommRing A] (I a : Ideal A)
    (F : (complementZeroLocus A a : Scheme).Modules)
    (k : unitModule (complementZeroLocus A a : Scheme) ⟶
      adicLimitObj (idealSheafNearVanishing A I a) F) :
    ∃ w, formalSectionHom A I a F w = k := by
  have hcompat : ∀ (m n : ℕᵒᵖ) (g : m ⟶ n),
      Scheme.Modules.Hom.app ((quotientSystemNearVanishing A I a F).map g) ⊤
          (globalSectionOfHom ((quotientSystemNearVanishing A I a F).obj m)
            (k ≫ limit.π (quotientSystemNearVanishing A I a F) m)) =
        globalSectionOfHom ((quotientSystemNearVanishing A I a F).obj n)
          (k ≫ limit.π (quotientSystemNearVanishing A I a F) n) := by
    intro m n g
    refine (globalSectionOfHom_comp _ _ _).symm.trans
      (congrArg (globalSectionOfHom ((quotientSystemNearVanishing A I a F).obj n)) ?_)
    exact (Category.assoc _ _ _).trans (congrArg (fun z => k ≫ z)
      (limit.w (quotientSystemNearVanishing A I a F) g))
  have hlim := isLimitOfPreserves (forget Ab.{u}) (limit.isLimit (formalSections A I a F))
  refine ⟨(Types.isLimitEquivSections hlim).symm
    ⟨fun n => globalSectionOfHom ((quotientSystemNearVanishing A I a F).obj n)
      (k ≫ limit.π (quotientSystemNearVanishing A I a F) n),
      fun {m n} g => hcompat m n g⟩, ?_⟩
  refine limit.hom_ext (F := quotientSystemNearVanishing A I a F) fun n => ?_
  refine hom_ext_of_globalSectionOfHom _ ?_
  refine (globalSectionOfHom_formalSectionHom_π A I a F _ n).trans ?_
  exact Types.isLimitEquivSections_symm_apply hlim _ n

/-! ### Restriction to a neighbourhood of the formal locus is faithful -/

/-- Two morphisms from the structure sheaf of `U` into a quotient `F / Iⁿ F` which agree after
restriction to a neighbourhood of the formal locus are equal: the quotient vanishes off the
support of `I · 𝒪_U`, so restriction is injective on its sections. -/
private theorem hom_eq_of_restrict_eq (A : Type u) [CommRing A] (I a : Ideal A)
    (F : (complementZeroLocus A a : Scheme).Modules) (V : OpensNearVanishing A I a) (n : ℕᵒᵖ)
    {f g : unitModule (complementZeroLocus A a : Scheme) ⟶
      (quotientSystemNearVanishing A I a F).obj n}
    (h : (Scheme.Modules.restrictFunctor V.openSet.ι).map f =
      (Scheme.Modules.restrictFunctor V.openSet.ι).map g) : f = g := by
  have happ : f.val.app (op V.openSet) (1 : Γ((complementZeroLocus A a : Scheme), V.openSet)) =
      g.val.app (op V.openSet) (1 : Γ((complementZeroLocus A a : Scheme), V.openSet)) :=
    localSectionHom_injective V.openSet ((quotientSystemNearVanishing A I a F).obj n)
      (((restrict_unit_hom_eq_localSectionHom V.openSet f).symm.trans h).trans
        (restrict_unit_hom_eq_localSectionHom V.openSet g))
  have hinj : Function.Injective (ConcreteCategory.hom (resNearVanishing A I a F V n)) :=
    ((ConcreteCategory.isIso_iff_bijective (resNearVanishing A I a F V n)).1 inferInstance).1
  refine hom_ext_of_globalSectionOfHom _ (hinj ?_)
  exact ((unit_hom_app_one _ f V.openSet).symm.trans happ).trans
    (unit_hom_app_one _ g V.openSet)

/-! ### The comparison map read through local sections -/

/-- The comparison map of a section defined on a neighbourhood `V` of the formal locus, read at
one level of the tower after restriction to `V`, is reduction modulo `Iⁿ`. -/
private theorem localSectionHom_comparison_π (A : Type u) [CommRing A] (I a : Ideal A)
    (F : (complementZeroLocus A a : Scheme).Modules) (V : OpensNearVanishing A I a)
    (t : Γ(F, V.openSet)) (n : ℕᵒᵖ) :
    localSectionHom V.openSet F t ≫ (Scheme.Modules.restrictFunctor V.openSet.ι).map
        (adicProj (idealSheafNearVanishing A I a) F n) =
      (Scheme.Modules.restrictFunctor V.openSet.ι).map
        (formalSectionHom A I a F (ConcreteCategory.hom (comparisonMap A I a F)
            (ConcreteCategory.hom (colimit.ι (sectionsNearVanishing A I a F) V) t)) ≫
          limit.π (quotientSystemNearVanishing A I a F) n) := by
  have hres : ((quotientSystemNearVanishing A I a F).obj n).presheaf.map
        (homOfLE (le_top (a := V.openSet))).op
        (formalSectionAt A I a F (ConcreteCategory.hom (comparisonMap A I a F)
          (ConcreteCategory.hom (colimit.ι (sectionsNearVanishing A I a F) V) t)) n) =
      Scheme.Modules.Hom.app (adicProj (idealSheafNearVanishing A I a) F n) V.openSet t :=
    ((ConcreteCategory.comp_apply (colimit.ι (sectionsNearVanishing A I a F) V) _ t).trans
        ((ConcreteCategory.comp_apply (comparisonMap A I a F) _ _).trans
          (ConcreteCategory.comp_apply
            (limit.π (formalSections A I a F) (op n.unop)) _ _))).symm.trans
      (ConcreteCategory.congr_hom (comparisonMap_restrict A I a F V n.unop) t)
  refine Eq.trans (localSectionHom_natural V.openSet t
      (adicProj (idealSheafNearVanishing A I a) F n)) ?_
  refine Eq.trans ?_ ((congrArg
    (fun k => (Scheme.Modules.restrictFunctor V.openSet.ι).map k)
      (formalSectionHom_π A I a F _ n)).trans
        (localSectionHom_homOfSection V.openSet _ _)).symm
  exact congrArg (localSectionHom V.openSet ((quotientSystemNearVanishing A I a F).obj n))
    hres.symm

/-- A morphism from the structure sheaf into the limit of the tower is the one attached to the
comparison of a section on a neighbourhood, once the two agree after restriction at every
level. -/
private theorem formalSectionHom_comparison_eq (A : Type u) [CommRing A] (I a : Ideal A)
    (F : (complementZeroLocus A a : Scheme).Modules) (V : OpensNearVanishing A I a)
    (t : Γ(F, V.openSet))
    (k : unitModule (complementZeroLocus A a : Scheme) ⟶
      adicLimitObj (idealSheafNearVanishing A I a) F)
    (h : ∀ n : ℕᵒᵖ, localSectionHom V.openSet F t ≫
        (Scheme.Modules.restrictFunctor V.openSet.ι).map
          (adicProj (idealSheafNearVanishing A I a) F n) =
      (Scheme.Modules.restrictFunctor V.openSet.ι).map
        (k ≫ limit.π (quotientSystemNearVanishing A I a F) n)) :
    formalSectionHom A I a F (ConcreteCategory.hom (comparisonMap A I a F)
      (ConcreteCategory.hom (colimit.ι (sectionsNearVanishing A I a F) V) t)) = k :=
  limit.hom_ext (F := quotientSystemNearVanishing A I a F) fun n =>
    hom_eq_of_restrict_eq A I a F V n
      ((localSectionHom_comparison_π A I a F V t n).symm.trans (h n))

/-- A formal section is the comparison of a section on a neighbourhood of the formal locus, once
the two agree after restriction at every level. -/
private theorem comparison_eq_of_localSectionHom_π (A : Type u) [CommRing A] (I a : Ideal A)
    (F : (complementZeroLocus A a : Scheme).Modules) (V : OpensNearVanishing A I a)
    (t : Γ(F, V.openSet)) (w : ToType (limit (formalSections A I a F)))
    (h : ∀ n : ℕᵒᵖ, localSectionHom V.openSet F t ≫
        (Scheme.Modules.restrictFunctor V.openSet.ι).map
          (adicProj (idealSheafNearVanishing A I a) F n) =
      (Scheme.Modules.restrictFunctor V.openSet.ι).map
        (formalSectionHom A I a F w ≫
          limit.π (quotientSystemNearVanishing A I a F) n)) :
    ConcreteCategory.hom (comparisonMap A I a F)
      (ConcreteCategory.hom (colimit.ι (sectionsNearVanishing A I a F) V) t) = w :=
  formalSectionHom_injective A I a F
    (formalSectionHom_comparison_eq A I a F V t (formalSectionHom A I a F w) h)

/-- Shrinking the neighbourhood does not change the comparison of a section. -/
private theorem comparisonMap_restrict_section (A : Type u) [CommRing A] (I a : Ideal A)
    (F : (complementZeroLocus A a : Scheme).Modules) (V W : OpensNearVanishing A I a)
    (hWV : W.openSet ≤ V.openSet) (t : Γ(F, V.openSet)) :
    ConcreteCategory.hom (comparisonMap A I a F)
        (ConcreteCategory.hom (colimit.ι (sectionsNearVanishing A I a F) W)
          (F.presheaf.map (homOfLE hWV).op t)) =
      ConcreteCategory.hom (comparisonMap A I a F)
        (ConcreteCategory.hom (colimit.ι (sectionsNearVanishing A I a F) V) t) := by
  have hw := (ConcreteCategory.comp_apply
      ((sectionsNearVanishing A I a F).map (show V ⟶ W from ⟨hWV⟩))
      (colimit.ι (sectionsNearVanishing A I a F) W) t).symm.trans
    (ConcreteCategory.congr_hom
      (colimit.w (sectionsNearVanishing A I a F) (show V ⟶ W from ⟨hWV⟩)) t)
  exact congrArg (ConcreteCategory.hom (comparisonMap A I a F)) hw

/-! ### Shrinking finitely many neighbourhoods to a common one -/

/-- The intersection of a finite family of neighbourhoods of the formal locus. -/
private def infNearVanishing (A : Type u) [CommRing A] (I a : Ideal A) {ι : Type*} [Finite ι]
    (V : ι → OpensNearVanishing A I a) : OpensNearVanishing A I a where
  openSet := ⨅ i, (V i).openSet
  contains_vanishing x hx := by
    have hmem : x ∈ ((⨅ i, (V i).openSet :
        (complementZeroLocus A a : Scheme).Opens) :
          Set (complementZeroLocus A a : Scheme)) := by
      rw [Opens.coe_iInf]
      exact Set.mem_iInter.2 fun i => (V i).contains_vanishing x hx
    exact hmem

/-- The intersection of two neighbourhoods of the formal locus. -/
private def interNearVanishing (A : Type u) [CommRing A] (I a : Ideal A)
    (V W : OpensNearVanishing A I a) : OpensNearVanishing A I a where
  openSet := V.openSet ⊓ W.openSet
  contains_vanishing x hx := ⟨V.contains_vanishing x hx, W.contains_vanishing x hx⟩

/-- A formal section in the image of the comparison map is the comparison of a section on some
neighbourhood of the formal locus. -/
private theorem exists_section_comparisonMap_eq (A : Type u) [CommRing A] (I a : Ideal A)
    (F : (complementZeroLocus A a : Scheme).Modules)
    (hF : Function.Surjective (ConcreteCategory.hom (comparisonMap A I a F)))
    (w : ToType (limit (formalSections A I a F))) :
    ∃ (V : OpensNearVanishing A I a) (t : Γ(F, V.openSet)),
      ConcreteCategory.hom (comparisonMap A I a F)
        (ConcreteCategory.hom (colimit.ι (sectionsNearVanishing A I a F) V) t) = w := by
  have hforget : PreservesFilteredColimitsOfSize.{0, u} (forget Ab.{u}) :=
    preservesFilteredColimitsOfSize_of_univLE.{u, u, 0, u} _
  obtain ⟨z, hz⟩ := hF w
  obtain ⟨V, t, rfl⟩ := Concrete.colimit_exists_rep (sectionsNearVanishing A I a F) z
  exact ⟨V, t, hz⟩

/-- Finitely many formal sections in the image of the comparison map are the comparisons of
sections on one common neighbourhood of the formal locus. -/
private theorem exists_sections_comparisonMap_eq (A : Type u) [CommRing A] (I a : Ideal A)
    (F : (complementZeroLocus A a : Scheme).Modules)
    (hF : Function.Surjective (ConcreteCategory.hom (comparisonMap A I a F)))
    {ι : Type*} [Finite ι] (w : ι → ToType (limit (formalSections A I a F))) :
    ∃ (V : OpensNearVanishing A I a) (t : ι → Γ(F, V.openSet)), ∀ i,
      ConcreteCategory.hom (comparisonMap A I a F)
        (ConcreteCategory.hom (colimit.ι (sectionsNearVanishing A I a F) V) (t i)) = w i := by
  choose V t ht using fun i => exists_section_comparisonMap_eq A I a F hF (w i)
  refine ⟨infNearVanishing A I a V, fun i => F.presheaf.map
    (homOfLE (show (infNearVanishing A I a V).openSet ≤ (V i).openSet from iInf_le _ i)).op
      (t i), fun i => ?_⟩
  exact (comparisonMap_restrict_section A I a F (V i) (infNearVanishing A I a V)
    (iInf_le _ i) (t i)).trans (ht i)

/-- A section on a neighbourhood of the formal locus whose comparison vanishes already vanishes
on a smaller neighbourhood, once the comparison map is injective. -/
private theorem exists_restrict_eq_zero_of_comparisonMap_eq_zero (A : Type u) [CommRing A]
    (I a : Ideal A) (F : (complementZeroLocus A a : Scheme).Modules)
    (hF : Function.Injective (ConcreteCategory.hom (comparisonMap A I a F)))
    (V : OpensNearVanishing A I a) (t : Γ(F, V.openSet))
    (ht : ConcreteCategory.hom (comparisonMap A I a F)
      (ConcreteCategory.hom (colimit.ι (sectionsNearVanishing A I a F) V) t) = 0) :
    ∃ (W : OpensNearVanishing A I a) (hWV : W.openSet ≤ V.openSet),
      F.presheaf.map (homOfLE hWV).op t = 0 := by
  have h0 : ConcreteCategory.hom (colimit.ι (sectionsNearVanishing A I a F) V) t = 0 :=
    hF (ht.trans (map_zero _).symm)
  obtain ⟨W, g, hg⟩ := exists_map_eq_zero_of_colimit_ι_eq_zero A I a F V t h0
  exact ⟨W, g.down, hg⟩

/-- Finitely many sections on a neighbourhood of the formal locus whose comparisons vanish all
vanish on one smaller neighbourhood. -/
private theorem exists_restrict_eq_zero_of_finite (A : Type u) [CommRing A] (I a : Ideal A)
    (F : (complementZeroLocus A a : Scheme).Modules)
    (hF : Function.Injective (ConcreteCategory.hom (comparisonMap A I a F)))
    (V : OpensNearVanishing A I a) {ι : Type*} [Finite ι] (t : ι → Γ(F, V.openSet))
    (ht : ∀ i, ConcreteCategory.hom (comparisonMap A I a F)
      (ConcreteCategory.hom (colimit.ι (sectionsNearVanishing A I a F) V) (t i)) = 0) :
    ∃ (W : OpensNearVanishing A I a) (hWV : W.openSet ≤ V.openSet),
      ∀ i, F.presheaf.map (homOfLE hWV).op (t i) = 0 := by
  choose W hW h using fun i =>
    exists_restrict_eq_zero_of_comparisonMap_eq_zero A I a F hF V (t i) (ht i)
  refine ⟨interNearVanishing A I a (infNearVanishing A I a W) V, inf_le_right, fun i => ?_⟩
  have hZW : (infNearVanishing A I a W).openSet ⊓ V.openSet ≤ (W i).openSet :=
    inf_le_left.trans (iInf_le _ i)
  have hcomp := ConcreteCategory.congr_hom
    (F.presheaf.map_comp (homOfLE (hW i)).op (homOfLE hZW).op) (t i)
  simp only [ConcreteCategory.comp_apply] at hcomp
  have he : (homOfLE (inf_le_right : (infNearVanishing A I a W).openSet ⊓ V.openSet ≤
      V.openSet)).op = (homOfLE (hW i)).op ≫ (homOfLE hZW).op := Subsingleton.elim _ _
  refine Eq.trans (congrArg
    (fun φ => ConcreteCategory.hom (F.presheaf.map φ) (t i)) he) ?_
  refine hcomp.trans ?_
  exact (congrArg (fun y => F.presheaf.map (homOfLE hZW).op y) (h i)).trans (map_zero _)

/-! ### The correction of a lifted generator -/

/-- A lifted generator of an ideal-power multiple, multiplied into a formal section of the middle
term and corrected by its own lift to the middle term, dies in the limit of the tower of the
third term, so it comes from a formal section of the first term. -/
private theorem exists_formal_correction (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I a : Ideal A) (S : ShortComplex (complementZeroLocus A a : Scheme).Modules)
    (hS : S.ShortExact) [S.X₁.IsCoherent] [S.X₂.IsCoherent] [S.X₃.IsCoherent]
    (w : ToType (limit (formalSections A I a S.X₂))) (V : OpensNearVanishing A I a)
    (t : Γ(S.X₃, V.openSet))
    (ht : ConcreteCategory.hom (comparisonMap A I a S.X₃)
      (ConcreteCategory.hom (colimit.ι (sectionsNearVanishing A I a S.X₃) V) t) =
        ConcreteCategory.hom (limMap (formalSectionsMap A I a S.g)) w)
    (c : unitModule (complementZeroLocus A a : Scheme) ⟶
      unitModule (complementZeroLocus A a : Scheme))
    (m : unitModule (complementZeroLocus A a : Scheme) ⟶ S.X₂)
    (hm : (Scheme.Modules.restrictFunctor V.openSet.ι).map (m ≫ S.g) =
      (Scheme.Modules.restrictFunctor V.openSet.ι).map c ≫
        localSectionHom V.openSet S.X₃ t) :
    ∃ l : ToType (limit (formalSections A I a S.X₁)),
      formalSectionHom A I a S.X₁ l ≫
          adicLimitMap (idealSheafNearVanishing A I a) S.f =
        c ≫ formalSectionHom A I a S.X₂ w -
          m ≫ adicLimitLift (idealSheafNearVanishing A I a) S.X₂ := by
  have hlevel : ∀ n : ℕᵒᵖ, c ≫ (formalSectionHom A I a S.X₂ w ≫
        limit.π (quotientSystemNearVanishing A I a S.X₂) n ≫
          (adicQuotientSystemMap (idealSheafNearVanishing A I a) S.g).app n) =
      m ≫ S.g ≫ adicProj (idealSheafNearVanishing A I a) S.X₃ n := by
    intro n
    refine hom_eq_of_restrict_eq A I a S.X₃ V n ?_
    have h2 := formalSectionHom_natural_π A I a S.g w n
    have h1 : (Scheme.Modules.restrictFunctor V.openSet.ι).map
          (formalSectionHom A I a S.X₃
              (ConcreteCategory.hom (limMap (formalSectionsMap A I a S.g)) w) ≫
            limit.π (quotientSystemNearVanishing A I a S.X₃) n) =
        localSectionHom V.openSet S.X₃ t ≫
          (Scheme.Modules.restrictFunctor V.openSet.ι).map
            (adicProj (idealSheafNearVanishing A I a) S.X₃ n) :=
      (congrArg (fun z => (Scheme.Modules.restrictFunctor V.openSet.ι).map
          (formalSectionHom A I a S.X₃ z ≫
            limit.π (quotientSystemNearVanishing A I a S.X₃) n)) ht).symm.trans
        (localSectionHom_comparison_π A I a S.X₃ V t n).symm
    calc (Scheme.Modules.restrictFunctor V.openSet.ι).map
            (c ≫ (formalSectionHom A I a S.X₂ w ≫
              limit.π (quotientSystemNearVanishing A I a S.X₂) n ≫
                (adicQuotientSystemMap (idealSheafNearVanishing A I a) S.g).app n))
          = (Scheme.Modules.restrictFunctor V.openSet.ι).map c ≫
              (Scheme.Modules.restrictFunctor V.openSet.ι).map
                (formalSectionHom A I a S.X₂ w ≫
                  limit.π (quotientSystemNearVanishing A I a S.X₂) n ≫
                    (adicQuotientSystemMap (idealSheafNearVanishing A I a) S.g).app n) :=
            (Scheme.Modules.restrictFunctor V.openSet.ι).map_comp _ _
        _ = (Scheme.Modules.restrictFunctor V.openSet.ι).map c ≫
              (localSectionHom V.openSet S.X₃ t ≫
                (Scheme.Modules.restrictFunctor V.openSet.ι).map
                  (adicProj (idealSheafNearVanishing A I a) S.X₃ n)) :=
            congrArg (fun z => (Scheme.Modules.restrictFunctor V.openSet.ι).map c ≫ z)
              ((congrArg (fun z => (Scheme.Modules.restrictFunctor V.openSet.ι).map z)
                h2).symm.trans h1)
        _ = ((Scheme.Modules.restrictFunctor V.openSet.ι).map c ≫
              localSectionHom V.openSet S.X₃ t) ≫
              (Scheme.Modules.restrictFunctor V.openSet.ι).map
                (adicProj (idealSheafNearVanishing A I a) S.X₃ n) :=
            (Category.assoc _ _ _).symm
        _ = (Scheme.Modules.restrictFunctor V.openSet.ι).map (m ≫ S.g) ≫
              (Scheme.Modules.restrictFunctor V.openSet.ι).map
                (adicProj (idealSheafNearVanishing A I a) S.X₃ n) :=
            congrArg (fun z => z ≫ (Scheme.Modules.restrictFunctor V.openSet.ι).map
              (adicProj (idealSheafNearVanishing A I a) S.X₃ n)) hm.symm
        _ = (Scheme.Modules.restrictFunctor V.openSet.ι).map
              ((m ≫ S.g) ≫ adicProj (idealSheafNearVanishing A I a) S.X₃ n) :=
            ((Scheme.Modules.restrictFunctor V.openSet.ι).map_comp _ _).symm
        _ = (Scheme.Modules.restrictFunctor V.openSet.ι).map
              (m ≫ S.g ≫ adicProj (idealSheafNearVanishing A I a) S.X₃ n) :=
            congrArg (fun z => (Scheme.Modules.restrictFunctor V.openSet.ι).map z)
              (Category.assoc _ _ _)
  obtain ⟨v, hv⟩ := exists_formalSection_of_hom A I a S.X₂
    (c ≫ formalSectionHom A I a S.X₂ w -
      m ≫ adicLimitLift (idealSheafNearVanishing A I a) S.X₂)
  have hzero : ConcreteCategory.hom (limMap (formalSectionsMap A I a S.g)) v = 0 := by
    refine formalSectionAt_ext A I a S.X₃ _ 0 fun n => ?_
    refine Eq.trans ?_ (formalSectionAt_zero A I a S.X₃ n).symm
    refine (formalSectionAt_limMap A I a S.g v n).trans ?_
    refine Eq.trans (congrArg (fun y => Scheme.Modules.Hom.app
        ((adicQuotientSystemMap (idealSheafNearVanishing A I a) S.g).app n) ⊤ y)
      (globalSectionOfHom_formalSectionHom_π A I a S.X₂ v n).symm) ?_
    refine (globalSectionOfHom_comp _ _ _).symm.trans ?_
    refine Eq.trans (congrArg
      (globalSectionOfHom ((quotientSystemNearVanishing A I a S.X₃).obj n)) ?_)
      (globalSectionOfHom_zero_hom ((quotientSystemNearVanishing A I a S.X₃).obj n))
    have hvn : (formalSectionHom A I a S.X₂ v ≫
          limit.π (quotientSystemNearVanishing A I a S.X₂) n) ≫
          (adicQuotientSystemMap (idealSheafNearVanishing A I a) S.g).app n =
        (c ≫ formalSectionHom A I a S.X₂ w -
            m ≫ adicLimitLift (idealSheafNearVanishing A I a) S.X₂) ≫
          limit.π (quotientSystemNearVanishing A I a S.X₂) n ≫
            (adicQuotientSystemMap (idealSheafNearVanishing A I a) S.g).app n :=
      (Category.assoc _ _ _).trans
        (congrArg (fun z => z ≫ limit.π (quotientSystemNearVanishing A I a S.X₂) n ≫
          (adicQuotientSystemMap (idealSheafNearVanishing A I a) S.g).app n) hv)
    have hR : (m ≫ adicLimitLift (idealSheafNearVanishing A I a) S.X₂) ≫
        limit.π (quotientSystemNearVanishing A I a S.X₂) n ≫
          (adicQuotientSystemMap (idealSheafNearVanishing A I a) S.g).app n =
        m ≫ S.g ≫ adicProj (idealSheafNearVanishing A I a) S.X₃ n :=
      (Category.assoc _ _ _).trans (congrArg (fun z => m ≫ z)
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun z => z ≫
              (adicQuotientSystemMap (idealSheafNearVanishing A I a) S.g).app n)
            (adicLimitLift_π (idealSheafNearVanishing A I a) S.X₂ n)).trans
            (adicProj_comp_adicQuotientSystemMap_app
              (idealSheafNearVanishing A I a) S.g n))))
    refine hvn.trans ?_
    rw [Preadditive.sub_comp, sub_eq_zero, Category.assoc]
    exact (hlevel n).trans hR.symm
  obtain ⟨l, hl⟩ := exists_limMap_formalSectionsMap_eq A I a S hS v hzero
  exact ⟨l, ((formalSectionHom_natural A I a S.f l).symm.trans
    (congrArg (formalSectionHom A I a S.X₂) hl)).trans hv⟩

/-- The corrected section `f(t) + m(1)` on a neighbourhood of the formal locus has the comparison
`c · ŝ` at every level of the tower: the correction `t` accounts exactly for the difference
between `c · ŝ` and the reduction of `m(1)`. -/
private theorem corrected_localSectionHom_π (A : Type u) [CommRing A] (I a : Ideal A)
    {F G : (complementZeroLocus A a : Scheme).Modules} (f : F ⟶ G)
    (w : ToType (limit (formalSections A I a G))) (l : ToType (limit (formalSections A I a F)))
    (c : unitModule (complementZeroLocus A a : Scheme) ⟶
      unitModule (complementZeroLocus A a : Scheme))
    (m : unitModule (complementZeroLocus A a : Scheme) ⟶ G)
    (hl : formalSectionHom A I a F l ≫
        adicLimitMap (idealSheafNearVanishing A I a) f =
      c ≫ formalSectionHom A I a G w -
        m ≫ adicLimitLift (idealSheafNearVanishing A I a) G)
    (V : OpensNearVanishing A I a) (t : Γ(F, V.openSet))
    (ht : ConcreteCategory.hom (comparisonMap A I a F)
      (ConcreteCategory.hom (colimit.ι (sectionsNearVanishing A I a F) V) t) = l) (n : ℕᵒᵖ) :
    localSectionHom V.openSet G
        (f.val.app (op V.openSet) t + m.val.app (op V.openSet)
          (1 : Γ((complementZeroLocus A a : Scheme), V.openSet))) ≫
        (Scheme.Modules.restrictFunctor V.openSet.ι).map
          (adicProj (idealSheafNearVanishing A I a) G n) =
      (Scheme.Modules.restrictFunctor V.openSet.ι).map
        (c ≫ formalSectionHom A I a G w ≫
          limit.π (quotientSystemNearVanishing A I a G) n) := by
  have he : formalSectionHom A I a F l ≫
        limit.π (quotientSystemNearVanishing A I a F) n ≫
          (adicQuotientSystemMap (idealSheafNearVanishing A I a) f).app n =
      c ≫ formalSectionHom A I a G w ≫
          limit.π (quotientSystemNearVanishing A I a G) n -
        m ≫ adicProj (idealSheafNearVanishing A I a) G n := by
    have h := congrArg (fun z => z ≫ limit.π (quotientSystemNearVanishing A I a G) n) hl
    rwa [Preadditive.sub_comp, Category.assoc, Category.assoc, Category.assoc, limMap_π,
      adicLimitLift_π] at h
  have key : c ≫ formalSectionHom A I a G w ≫
        limit.π (quotientSystemNearVanishing A I a G) n =
      formalSectionHom A I a F l ≫
          limit.π (quotientSystemNearVanishing A I a F) n ≫
            (adicQuotientSystemMap (idealSheafNearVanishing A I a) f).app n +
        m ≫ adicProj (idealSheafNearVanishing A I a) G n :=
    sub_eq_iff_eq_add.mp he.symm
  have hfirst : localSectionHom V.openSet G (f.val.app (op V.openSet) t) =
      localSectionHom V.openSet F t ≫
        (Scheme.Modules.restrictFunctor V.openSet.ι).map f :=
    (localSectionHom_natural V.openSet t f).symm
  have hsecond : localSectionHom V.openSet G (m.val.app (op V.openSet)
        (1 : Γ((complementZeroLocus A a : Scheme), V.openSet))) =
      (Scheme.Modules.restrictFunctor V.openSet.ι).map m :=
    (restrict_unit_hom_eq_localSectionHom V.openSet m).symm
  have hsum : localSectionHom V.openSet G
        (f.val.app (op V.openSet) t + m.val.app (op V.openSet)
          (1 : Γ((complementZeroLocus A a : Scheme), V.openSet))) =
      localSectionHom V.openSet F t ≫
          (Scheme.Modules.restrictFunctor V.openSet.ι).map f +
        (Scheme.Modules.restrictFunctor V.openSet.ι).map m :=
    (localSectionHom_add V.openSet G _ _).trans (by rw [hfirst, hsecond])
  have hA : (localSectionHom V.openSet F t ≫
        (Scheme.Modules.restrictFunctor V.openSet.ι).map f) ≫
        (Scheme.Modules.restrictFunctor V.openSet.ι).map
          (adicProj (idealSheafNearVanishing A I a) G n) =
      (Scheme.Modules.restrictFunctor V.openSet.ι).map
        (formalSectionHom A I a F l ≫
          limit.π (quotientSystemNearVanishing A I a F) n ≫
            (adicQuotientSystemMap (idealSheafNearVanishing A I a) f).app n) :=
    calc (localSectionHom V.openSet F t ≫
            (Scheme.Modules.restrictFunctor V.openSet.ι).map f) ≫
            (Scheme.Modules.restrictFunctor V.openSet.ι).map
              (adicProj (idealSheafNearVanishing A I a) G n)
          = localSectionHom V.openSet F t ≫
              (Scheme.Modules.restrictFunctor V.openSet.ι).map
                (f ≫ adicProj (idealSheafNearVanishing A I a) G n) :=
            (Category.assoc _ _ _).trans
              (congrArg (fun z => localSectionHom V.openSet F t ≫ z)
                ((Scheme.Modules.restrictFunctor V.openSet.ι).map_comp _ _).symm)
      _ = (localSectionHom V.openSet F t ≫
              (Scheme.Modules.restrictFunctor V.openSet.ι).map
                (adicProj (idealSheafNearVanishing A I a) F n)) ≫
              (Scheme.Modules.restrictFunctor V.openSet.ι).map
                ((adicQuotientSystemMap (idealSheafNearVanishing A I a) f).app n) :=
            ((congrArg (fun z => localSectionHom V.openSet F t ≫
                (Scheme.Modules.restrictFunctor V.openSet.ι).map z)
              (adicProj_comp_adicQuotientSystemMap_app
                (idealSheafNearVanishing A I a) f n)).symm.trans
              (congrArg (fun z => localSectionHom V.openSet F t ≫ z)
                ((Scheme.Modules.restrictFunctor V.openSet.ι).map_comp _ _))).trans
              (Category.assoc _ _ _).symm
      _ = (Scheme.Modules.restrictFunctor V.openSet.ι).map
              (formalSectionHom A I a F l ≫
                limit.π (quotientSystemNearVanishing A I a F) n) ≫
              (Scheme.Modules.restrictFunctor V.openSet.ι).map
                ((adicQuotientSystemMap (idealSheafNearVanishing A I a) f).app n) :=
            congrArg (fun z => z ≫ (Scheme.Modules.restrictFunctor V.openSet.ι).map
                ((adicQuotientSystemMap (idealSheafNearVanishing A I a) f).app n))
              ((localSectionHom_comparison_π A I a F V t n).trans
                (congrArg (fun y => (Scheme.Modules.restrictFunctor V.openSet.ι).map
                  (formalSectionHom A I a F y ≫
                    limit.π (quotientSystemNearVanishing A I a F) n)) ht))
      _ = (Scheme.Modules.restrictFunctor V.openSet.ι).map
              (formalSectionHom A I a F l ≫
                limit.π (quotientSystemNearVanishing A I a F) n ≫
                  (adicQuotientSystemMap (idealSheafNearVanishing A I a) f).app n) :=
            ((Scheme.Modules.restrictFunctor V.openSet.ι).map_comp _ _).symm.trans
              (congrArg (fun z => (Scheme.Modules.restrictFunctor V.openSet.ι).map z)
                (Category.assoc _ _ _))
  have hB : (Scheme.Modules.restrictFunctor V.openSet.ι).map m ≫
        (Scheme.Modules.restrictFunctor V.openSet.ι).map
          (adicProj (idealSheafNearVanishing A I a) G n) =
      (Scheme.Modules.restrictFunctor V.openSet.ι).map
        (m ≫ adicProj (idealSheafNearVanishing A I a) G n) :=
    ((Scheme.Modules.restrictFunctor V.openSet.ι).map_comp _ _).symm
  calc localSectionHom V.openSet G
          (f.val.app (op V.openSet) t + m.val.app (op V.openSet)
            (1 : Γ((complementZeroLocus A a : Scheme), V.openSet))) ≫
          (Scheme.Modules.restrictFunctor V.openSet.ι).map
            (adicProj (idealSheafNearVanishing A I a) G n)
        = (localSectionHom V.openSet F t ≫
              (Scheme.Modules.restrictFunctor V.openSet.ι).map f +
            (Scheme.Modules.restrictFunctor V.openSet.ι).map m) ≫
            (Scheme.Modules.restrictFunctor V.openSet.ι).map
              (adicProj (idealSheafNearVanishing A I a) G n) :=
          congrArg (fun z => z ≫ (Scheme.Modules.restrictFunctor V.openSet.ι).map
            (adicProj (idealSheafNearVanishing A I a) G n)) hsum
    _ = (Scheme.Modules.restrictFunctor V.openSet.ι).map
            (formalSectionHom A I a F l ≫
              limit.π (quotientSystemNearVanishing A I a F) n ≫
                (adicQuotientSystemMap (idealSheafNearVanishing A I a) f).app n) +
          (Scheme.Modules.restrictFunctor V.openSet.ι).map
            (m ≫ adicProj (idealSheafNearVanishing A I a) G n) := by
          rw [Preadditive.add_comp, hA, hB]
    _ = (Scheme.Modules.restrictFunctor V.openSet.ι).map
            (formalSectionHom A I a F l ≫
                limit.π (quotientSystemNearVanishing A I a F) n ≫
                  (adicQuotientSystemMap (idealSheafNearVanishing A I a) f).app n +
              m ≫ adicProj (idealSheafNearVanishing A I a) G n) :=
          ((Scheme.Modules.restrictFunctor V.openSet.ι).map_add).symm
    _ = (Scheme.Modules.restrictFunctor V.openSet.ι).map
            (c ≫ formalSectionHom A I a G w ≫
              limit.π (quotientSystemNearVanishing A I a G) n) :=
          congrArg (fun z => (Scheme.Modules.restrictFunctor V.openSet.ι).map z) key.symm


/-! ### Restriction to an open is right exact -/

/-- Restriction to an open carries an epimorphism to an epimorphism: it is a left adjoint. -/
private theorem epi_restrict_map {X : Scheme.{u}} (Z : X.Opens) {E G : X.Modules} (f : E ⟶ G)
    (hf : Epi f) : Epi ((Scheme.Modules.restrictFunctor Z.ι).map f) := by
  have : (Scheme.Modules.restrictFunctor Z.ι).IsLeftAdjoint :=
    (Scheme.Modules.restrictAdjunction Z.ι).isLeftAdjoint
  exact Functor.map_epi _ f

/-- Restriction to an open preserves the cokernel of the kernel inclusion of an epimorphism: a
morphism out of the restriction of a module which kills the restriction of the kernel factors
through the restriction of the epimorphism. -/
private theorem exists_restrict_desc {X : Scheme.{u}} (Z : X.Opens) {E G : X.Modules}
    (f : E ⟶ G) (hf : Epi f) {M : Z.toScheme.Modules}
    (g : (Scheme.Modules.restrictFunctor Z.ι).obj E ⟶ M)
    (hg : (Scheme.Modules.restrictFunctor Z.ι).map (kernel.ι f) ≫ g = 0) :
    ∃ d, (Scheme.Modules.restrictFunctor Z.ι).map f ≫ d = g := by
  have : (Scheme.Modules.restrictFunctor Z.ι).IsLeftAdjoint :=
    (Scheme.Modules.restrictAdjunction Z.ι).isLeftAdjoint
  have : PreservesColimitsOfSize.{u, u} (Scheme.Modules.restrictFunctor Z.ι) := inferInstance
  have : PreservesColimitsOfSize.{0, 0} (Scheme.Modules.restrictFunctor Z.ι) :=
    preservesColimitsOfSize_shrink _
  have : PreservesFiniteColimits (Scheme.Modules.restrictFunctor Z.ι) := inferInstance
  have : Epi ((Scheme.Modules.restrictFunctor Z.ι).map f) := epi_restrict_map Z f hf
  have : Epi (((ShortComplex.mk (kernel.ι f) f (kernel.condition f)).map
      (Scheme.Modules.restrictFunctor Z.ι)).g) := epi_restrict_map Z f hf
  exact ((ShortComplex.exact_kernel f).map_of_epi_of_preservesCokernel
    (Scheme.Modules.restrictFunctor Z.ι) hf inferInstance).desc' g hg

/-! ### From a finite lift to a section -/

/-- A finite family of sections of `F` on a neighbourhood of the formal locus whose comparisons
are the generators of an ideal-power multiple applied to a formal section `ŝ` assembles, after
shrinking the neighbourhood, into a single section whose comparison is `ŝ`.

The relations between the generators are finitely many, because the kernel of the presentation is
coherent, and each of them holds for the family after shrinking, because the comparison map is
injective; the family then factors through the ideal-power multiple, which is the structure sheaf
on the smaller neighbourhood. -/
private theorem exists_section_of_finite_lift (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I a : Ideal A) (F : (complementZeroLocus A a : Scheme).Modules) [F.IsCoherent]
    (hF : Function.Injective (ConcreteCategory.hom (comparisonMap A I a F)))
    (w : ToType (limit (formalSections A I a F))) (V : OpensNearVanishing A I a)
    {ι : Type u} [Finite ι]
    (N : (complementZeroLocus A a : Scheme).Modules)
    (p : SheafOfModules.free (R := (complementZeroLocus A a : Scheme).ringCatSheaf) ι ⟶ N)
    (hp : Epi p) (hker : (kernel p).IsCoherent)
    (j : N ⟶ unitModule (complementZeroLocus A a : Scheme))
    (hj : ∀ Z : OpensNearVanishing A I a, Z.openSet ≤ V.openSet →
      IsIso ((Scheme.Modules.restrictFunctor Z.openSet.ι).map j))
    (t : ι → Γ(F, V.openSet))
    (ht : ∀ (i : ι) (n : ℕᵒᵖ), localSectionHom V.openSet F (t i) ≫
        (Scheme.Modules.restrictFunctor V.openSet.ι).map
          (adicProj (idealSheafNearVanishing A I a) F n) =
      (Scheme.Modules.restrictFunctor V.openSet.ι).map
        ((SheafOfModules.ιFree i ≫ p ≫ j) ≫ formalSectionHom A I a F w ≫
          limit.π (quotientSystemNearVanishing A I a F) n)) :
    ∃ z, ConcreteCategory.hom (comparisonMap A I a F) z = w := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  have : Epi p := hp
  have : (kernel p).IsCoherent := hker
  have ht' : ∀ i : ι, formalSectionHom A I a F (ConcreteCategory.hom (comparisonMap A I a F)
      (ConcreteCategory.hom (colimit.ι (sectionsNearVanishing A I a F) V) (t i))) =
      (SheafOfModules.ιFree i ≫ p ≫ j) ≫ formalSectionHom A I a F w := fun i =>
    formalSectionHom_comparison_eq A I a F V (t i) _ fun n => (ht i n).trans
      (congrArg (fun z => (Scheme.Modules.restrictFunctor V.openSet.ι).map z)
        (Category.assoc _ _ _).symm)
  have hloc : ∀ (Z : OpensNearVanishing A I a) (hZV : Z.openSet ≤ V.openSet) (n : ℕᵒᵖ),
      localFreeHom Z.openSet F (fun i => F.presheaf.map (homOfLE hZV).op (t i)) ≫
          (Scheme.Modules.restrictFunctor Z.openSet.ι).map
            (adicProj (idealSheafNearVanishing A I a) F n) =
        (Scheme.Modules.restrictFunctor Z.openSet.ι).map (p ≫ j) ≫
          (Scheme.Modules.restrictFunctor Z.openSet.ι).map
            (formalSectionHom A I a F w ≫
              limit.π (quotientSystemNearVanishing A I a F) n) := by
    intro Z hZV n
    refine localFreeHom_ext Z.openSet fun i => ?_
    calc (Scheme.Modules.restrictFunctor Z.openSet.ι).map (SheafOfModules.ιFree i) ≫
            (localFreeHom Z.openSet F (fun i => F.presheaf.map (homOfLE hZV).op (t i)) ≫
              (Scheme.Modules.restrictFunctor Z.openSet.ι).map
                (adicProj (idealSheafNearVanishing A I a) F n))
          = localSectionHom Z.openSet F (F.presheaf.map (homOfLE hZV).op (t i)) ≫
              (Scheme.Modules.restrictFunctor Z.openSet.ι).map
                (adicProj (idealSheafNearVanishing A I a) F n) :=
          (Category.assoc _ _ _).symm.trans
            (congrArg (fun z => z ≫ (Scheme.Modules.restrictFunctor Z.openSet.ι).map
                (adicProj (idealSheafNearVanishing A I a) F n))
              (localFreeHom_ι Z.openSet F _ i))
      _ = (Scheme.Modules.restrictFunctor Z.openSet.ι).map
            (((SheafOfModules.ιFree i ≫ p ≫ j) ≫ formalSectionHom A I a F w) ≫
              limit.π (quotientSystemNearVanishing A I a F) n) :=
          ((localSectionHom_comparison_π A I a F Z _ n).trans
            (congrArg (fun y => (Scheme.Modules.restrictFunctor Z.openSet.ι).map
                (formalSectionHom A I a F y ≫
                  limit.π (quotientSystemNearVanishing A I a F) n))
              (comparisonMap_restrict_section A I a F V Z hZV (t i)))).trans
            (congrArg (fun y => (Scheme.Modules.restrictFunctor Z.openSet.ι).map
                (y ≫ limit.π (quotientSystemNearVanishing A I a F) n)) (ht' i))
      _ = (Scheme.Modules.restrictFunctor Z.openSet.ι).map
            (SheafOfModules.ιFree i ≫ (p ≫ j) ≫ formalSectionHom A I a F w ≫
              limit.π (quotientSystemNearVanishing A I a F) n) :=
          congrArg (fun z => (Scheme.Modules.restrictFunctor Z.openSet.ι).map z)
            ((Category.assoc _ _ _).trans (Category.assoc _ _ _))
      _ = (Scheme.Modules.restrictFunctor Z.openSet.ι).map (SheafOfModules.ιFree i) ≫
            ((Scheme.Modules.restrictFunctor Z.openSet.ι).map (p ≫ j) ≫
              (Scheme.Modules.restrictFunctor Z.openSet.ι).map
                (formalSectionHom A I a F w ≫
                  limit.π (quotientSystemNearVanishing A I a F) n)) :=
          ((Scheme.Modules.restrictFunctor Z.openSet.ι).map_comp _ _).trans
            (congrArg (fun z => (Scheme.Modules.restrictFunctor Z.openSet.ι).map
                (SheafOfModules.ιFree i) ≫ z)
              ((Scheme.Modules.restrictFunctor Z.openSet.ι).map_comp _ _))
  obtain ⟨κ, hκ, q, hq⟩ := @exists_epi_free_of_isCoherent A _ _ a (kernel p) hker
  have : Fintype κ := Fintype.ofFinite κ
  have : Epi q := hq
  have hrfl : ∀ (hVV : V.openSet ≤ V.openSet) (i : ι),
      F.presheaf.map (homOfLE hVV).op (t i) = t i := by
    intro hVV i
    have h1 : (homOfLE hVV).op = 𝟙 (op V.openSet) := Subsingleton.elim _ _
    simp only [h1, F.presheaf.map_id, CategoryTheory.id_apply]
  have hv : ∀ i : κ, ConcreteCategory.hom (comparisonMap A I a F)
      (ConcreteCategory.hom (colimit.ι (sectionsNearVanishing A I a F) V)
        (∑ b, unitHomScalar ((SheafOfModules.ιFree i ≫ q ≫ kernel.ι p) ≫
          SheafOfModules.freeProjection b) V.openSet • t b)) = 0 := by
    intro i
    refine comparison_eq_of_localSectionHom_π A I a F V _ 0 fun n => ?_
    refine Eq.trans ?_ (restrict_formalSectionHom_zero A I a F V n).symm
    have hzero : (SheafOfModules.ιFree i ≫ q ≫ kernel.ι p) ≫ (p ≫ j) = 0 :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun z => SheafOfModules.ιFree i ≫ z)
            (((Category.assoc q (kernel.ι p) (p ≫ j)).trans
                (congrArg (fun z => q ≫ z)
                  (((Category.assoc (kernel.ι p) p j).symm.trans
                      (congrArg (fun z => z ≫ j) (kernel.condition p))).trans
                    zero_comp))).trans comp_zero)).trans comp_zero)
    have hV := hloc V le_rfl n
    rw [funext (hrfl le_rfl)] at hV
    calc localSectionHom V.openSet F
            (∑ b, unitHomScalar ((SheafOfModules.ιFree i ≫ q ≫ kernel.ι p) ≫
              SheafOfModules.freeProjection b) V.openSet • t b) ≫
            (Scheme.Modules.restrictFunctor V.openSet.ι).map
              (adicProj (idealSheafNearVanishing A I a) F n)
          = (Scheme.Modules.restrictFunctor V.openSet.ι).map
              (SheafOfModules.ιFree i ≫ q ≫ kernel.ι p) ≫
              (localFreeHom V.openSet F t ≫
                (Scheme.Modules.restrictFunctor V.openSet.ι).map
                  (adicProj (idealSheafNearVanishing A I a) F n)) :=
          (congrArg (fun z => z ≫ (Scheme.Modules.restrictFunctor V.openSet.ι).map
              (adicProj (idealSheafNearVanishing A I a) F n))
            (localFreeHom_precomp V.openSet F t _).symm).trans (Category.assoc _ _ _)
      _ = (Scheme.Modules.restrictFunctor V.openSet.ι).map
              (SheafOfModules.ιFree i ≫ q ≫ kernel.ι p) ≫
              ((Scheme.Modules.restrictFunctor V.openSet.ι).map (p ≫ j) ≫
                (Scheme.Modules.restrictFunctor V.openSet.ι).map
                  (formalSectionHom A I a F w ≫
                    limit.π (quotientSystemNearVanishing A I a F) n)) :=
          congrArg (fun z => (Scheme.Modules.restrictFunctor V.openSet.ι).map
            (SheafOfModules.ιFree i ≫ q ≫ kernel.ι p) ≫ z) hV
      _ = 0 :=
          (Category.assoc _ _ _).symm.trans
            ((congrArg (fun z => z ≫ (Scheme.Modules.restrictFunctor V.openSet.ι).map
                (formalSectionHom A I a F w ≫
                  limit.π (quotientSystemNearVanishing A I a F) n))
              (((Scheme.Modules.restrictFunctor V.openSet.ι).map_comp _ _).symm.trans
                ((congrArg (fun z => (Scheme.Modules.restrictFunctor V.openSet.ι).map z)
                  hzero).trans
                  ((Scheme.Modules.restrictFunctor V.openSet.ι).map_zero _ _)))).trans
              zero_comp)
  obtain ⟨Z, hZV, hZ⟩ := exists_restrict_eq_zero_of_finite A I a F hF V _ hv
  have : Epi ((Scheme.Modules.restrictFunctor Z.openSet.ι).map q) :=
    epi_restrict_map Z.openSet q hq
  have : Epi ((Scheme.Modules.restrictFunctor Z.openSet.ι).map p) :=
    epi_restrict_map Z.openSet p hp
  have hcomb : ∀ i : κ, (Scheme.Modules.restrictFunctor Z.openSet.ι).map
        (SheafOfModules.ιFree i ≫ q ≫ kernel.ι p) ≫
        localFreeHom Z.openSet F (fun i => F.presheaf.map (homOfLE hZV).op (t i)) = 0 := fun i =>
    (localFreeHom_precomp Z.openSet F _ _).trans
      ((congrArg (localSectionHom Z.openSet F)
        ((restrict_linearCombination F hZV t
          (SheafOfModules.ιFree i ≫ q ≫ kernel.ι p)).symm.trans (hZ i))).trans
        (localSectionHom_zero Z.openSet F))
  have hg : (Scheme.Modules.restrictFunctor Z.openSet.ι).map (kernel.ι p) ≫
      localFreeHom Z.openSet F (fun i => F.presheaf.map (homOfLE hZV).op (t i)) = 0 := by
    refine (cancel_epi ((Scheme.Modules.restrictFunctor Z.openSet.ι).map q)).1 ?_
    refine localFreeHom_ext Z.openSet fun i => ?_
    have hreassoc : (Scheme.Modules.restrictFunctor Z.openSet.ι).map
          (SheafOfModules.ιFree i ≫ q ≫ kernel.ι p) ≫
          localFreeHom Z.openSet F (fun i => F.presheaf.map (homOfLE hZV).op (t i)) =
        (Scheme.Modules.restrictFunctor Z.openSet.ι).map (SheafOfModules.ιFree i) ≫
          ((Scheme.Modules.restrictFunctor Z.openSet.ι).map q ≫
            ((Scheme.Modules.restrictFunctor Z.openSet.ι).map (kernel.ι p) ≫
              localFreeHom Z.openSet F
                (fun i => F.presheaf.map (homOfLE hZV).op (t i)))) :=
      (congrArg (fun z => z ≫ localFreeHom Z.openSet F
            (fun i => F.presheaf.map (homOfLE hZV).op (t i)))
          (((Scheme.Modules.restrictFunctor Z.openSet.ι).map_comp _ _).trans
            (congrArg (fun z => (Scheme.Modules.restrictFunctor Z.openSet.ι).map
                (SheafOfModules.ιFree i) ≫ z)
              ((Scheme.Modules.restrictFunctor Z.openSet.ι).map_comp _ _)))).trans
        ((Category.assoc _ _ _).trans
          (congrArg (fun z => (Scheme.Modules.restrictFunctor Z.openSet.ι).map
              (SheafOfModules.ιFree i) ≫ z) (Category.assoc _ _ _)))
    exact hreassoc.symm.trans ((hcomb i).trans
      (((congrArg (fun z => (Scheme.Modules.restrictFunctor Z.openSet.ι).map
          (SheafOfModules.ιFree i) ≫ z) comp_zero).trans comp_zero).symm))
  obtain ⟨d, hd⟩ := exists_restrict_desc Z.openSet p hp
    (localFreeHom Z.openSet F (fun i => F.presheaf.map (homOfLE hZV).op (t i))) hg
  have hjZ : IsIso ((Scheme.Modules.restrictFunctor Z.openSet.ι).map j) := hj Z hZV
  have hpj : (Scheme.Modules.restrictFunctor Z.openSet.ι).map (p ≫ j) =
      (Scheme.Modules.restrictFunctor Z.openSet.ι).map p ≫
        (Scheme.Modules.restrictFunctor Z.openSet.ι).map j :=
    (Scheme.Modules.restrictFunctor Z.openSet.ι).map_comp p j
  have hepi : Epi ((Scheme.Modules.restrictFunctor Z.openSet.ι).map (p ≫ j)) := by
    rw [hpj]
    infer_instance
  obtain ⟨z, hz⟩ := localSectionHom_surjective Z.openSet F
    (inv ((Scheme.Modules.restrictFunctor Z.openSet.ι).map j) ≫ d)
  refine ⟨ConcreteCategory.hom (colimit.ι (sectionsNearVanishing A I a F) Z) z,
    comparison_eq_of_localSectionHom_π A I a F Z z w fun n => ?_⟩
  refine (cancel_epi ((Scheme.Modules.restrictFunctor Z.openSet.ι).map (p ≫ j))).1 ?_
  refine Eq.trans ?_ (hloc Z hZV n)
  rw [hz, hpj, Category.assoc, Category.assoc, IsIso.hom_inv_id_assoc, ← Category.assoc, hd]

/-! ### The middle comparison of Stacks 0H48 -/

/-- **Stacks 0H48, the middle comparison.** For a short exact sequence `0 → F' → F → F'' → 0` of
coherent modules on `U = Spec(A) ∖ V(𝔞)` with `A` Noetherian, if the comparison maps of
`Stacks.Algebraization.comparisonMap` for `F'` and `F''` are isomorphisms, so is that for `F`. -/
@[stacks 0H48 "middle comparison"]
theorem isIso_comparisonMap_middle_of_ends (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I a : Ideal A) (S : ShortComplex (complementZeroLocus A a : Scheme).Modules)
    (hS : S.ShortExact) [S.X₁.IsCoherent] [S.X₂.IsCoherent] [S.X₃.IsCoherent]
    (h₁ : IsIso (comparisonMap A I a S.X₁)) (h₃ : IsIso (comparisonMap A I a S.X₃)) :
    IsIso (comparisonMap A I a S.X₂) := by
  classical
  have hb₁ := (ConcreteCategory.isIso_iff_bijective (comparisonMap A I a S.X₁)).1 h₁
  have hb₃ := (ConcreteCategory.isIso_iff_bijective (comparisonMap A I a S.X₃)).1 h₃
  have hinj : Function.Injective (ConcreteCategory.hom (comparisonMap A I a S.X₂)) :=
    injective_comparisonMap_middle_of_shortExact A I a S hS hb₁.1 hb₃.1
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨hinj, fun ŝ => ?_⟩
  obtain ⟨V, t, ht⟩ := exists_section_comparisonMap_eq A I a S.X₃ hb₃.2
    (ConcreteCategory.hom (limMap (formalSectionsMap A I a S.g)) ŝ)
  obtain ⟨K, n, φ, ι, hι, m, p, hp, hker, hcomm, hsupp, hφ⟩ :=
    exists_finite_lifting_generators A a S hS V.openSet t
  have hiso : IsIso ((Scheme.Modules.restrictFunctor V.openSet.ι).map
      (idealPowerMultiple K n (unitModule (complementZeroLocus A a : Scheme))).ι) :=
    isIso_restrict_idealPowerMultiple_ι K n _ V.openSet hsupp
  have h1 : localSectionHom V.openSet
        (idealPowerMultiple K n
          (unitModule (complementZeroLocus A a : Scheme))).toSheafOfModules
        ⟨(1 : Γ((complementZeroLocus A a : Scheme), V.openSet)),
          mem_idealPowerMultiple_of_disjoint_support K n
            (unitModule (complementZeroLocus A a : Scheme)) V.openSet hsupp
            (1 : Γ((complementZeroLocus A a : Scheme), V.openSet))⟩ ≫
      (Scheme.Modules.restrictFunctor V.openSet.ι).map
        (idealPowerMultiple K n (unitModule (complementZeroLocus A a : Scheme))).ι = 𝟙 _ :=
    (localSectionHom_natural V.openSet _ _).trans (localSectionHom_one V.openSet)
  have h2 : localSectionHom V.openSet
        (idealPowerMultiple K n
          (unitModule (complementZeroLocus A a : Scheme))).toSheafOfModules
        ⟨(1 : Γ((complementZeroLocus A a : Scheme), V.openSet)),
          mem_idealPowerMultiple_of_disjoint_support K n
            (unitModule (complementZeroLocus A a : Scheme)) V.openSet hsupp
            (1 : Γ((complementZeroLocus A a : Scheme), V.openSet))⟩ =
      inv ((Scheme.Modules.restrictFunctor V.openSet.ι).map
        (idealPowerMultiple K n (unitModule (complementZeroLocus A a : Scheme))).ι) :=
    (cancel_mono ((Scheme.Modules.restrictFunctor V.openSet.ι).map
      (idealPowerMultiple K n (unitModule (complementZeroLocus A a : Scheme))).ι)).1
      (h1.trans (IsIso.inv_hom_id _).symm)
  have hφ' : (Scheme.Modules.restrictFunctor V.openSet.ι).map φ =
      (Scheme.Modules.restrictFunctor V.openSet.ι).map
          (idealPowerMultiple K n (unitModule (complementZeroLocus A a : Scheme))).ι ≫
        localSectionHom V.openSet S.X₃ t := by
    refine (cancel_epi (inv ((Scheme.Modules.restrictFunctor V.openSet.ι).map
      (idealPowerMultiple K n (unitModule (complementZeroLocus A a : Scheme))).ι))).1 ?_
    rw [← h2, ← Category.assoc, h1, Category.id_comp]
    exact (localSectionHom_natural V.openSet _ φ).trans
      (congrArg (localSectionHom V.openSet S.X₃) (hφ _ rfl))
  have hm' : ∀ i : ι, (Scheme.Modules.restrictFunctor V.openSet.ι).map
        ((SheafOfModules.ιFree i ≫ m) ≫ S.g) =
      (Scheme.Modules.restrictFunctor V.openSet.ι).map (SheafOfModules.ιFree i ≫ p ≫
          (idealPowerMultiple K n (unitModule (complementZeroLocus A a : Scheme))).ι) ≫
        localSectionHom V.openSet S.X₃ t := fun i =>
    calc (Scheme.Modules.restrictFunctor V.openSet.ι).map
            ((SheafOfModules.ιFree i ≫ m) ≫ S.g)
          = (Scheme.Modules.restrictFunctor V.openSet.ι).map
              (SheafOfModules.ιFree i ≫ p ≫ φ) :=
          congrArg (fun z => (Scheme.Modules.restrictFunctor V.openSet.ι).map z)
            ((Category.assoc _ _ _).trans
              (congrArg (fun z => SheafOfModules.ιFree i ≫ z) hcomm))
      _ = (Scheme.Modules.restrictFunctor V.openSet.ι).map (SheafOfModules.ιFree i ≫ p) ≫
            (Scheme.Modules.restrictFunctor V.openSet.ι).map φ :=
          (congrArg (fun z => (Scheme.Modules.restrictFunctor V.openSet.ι).map z)
            (Category.assoc _ _ _).symm).trans
            ((Scheme.Modules.restrictFunctor V.openSet.ι).map_comp _ _)
      _ = (Scheme.Modules.restrictFunctor V.openSet.ι).map (SheafOfModules.ιFree i ≫ p) ≫
            ((Scheme.Modules.restrictFunctor V.openSet.ι).map
                (idealPowerMultiple K n
                  (unitModule (complementZeroLocus A a : Scheme))).ι ≫
              localSectionHom V.openSet S.X₃ t) :=
          congrArg (fun z => (Scheme.Modules.restrictFunctor V.openSet.ι).map
            (SheafOfModules.ιFree i ≫ p) ≫ z) hφ'
      _ = (Scheme.Modules.restrictFunctor V.openSet.ι).map (SheafOfModules.ιFree i ≫ p ≫
            (idealPowerMultiple K n
              (unitModule (complementZeroLocus A a : Scheme))).ι) ≫
            localSectionHom V.openSet S.X₃ t :=
          (Category.assoc _ _ _).symm.trans
            (congrArg (fun z => z ≫ localSectionHom V.openSet S.X₃ t)
              (((Scheme.Modules.restrictFunctor V.openSet.ι).map_comp _ _).symm.trans
                (congrArg (fun z => (Scheme.Modules.restrictFunctor V.openSet.ι).map z)
                  (Category.assoc _ _ _))))
  choose l hl using fun i : ι => exists_formal_correction A I a S hS ŝ V t ht
    (SheafOfModules.ιFree i ≫ p ≫
      (idealPowerMultiple K n (unitModule (complementZeroLocus A a : Scheme))).ι)
    (SheafOfModules.ιFree i ≫ m) (hm' i)
  obtain ⟨W₀, t₀, ht₀⟩ := exists_sections_comparisonMap_eq A I a S.X₁ hb₁.2 l
  let W := interNearVanishing A I a W₀ V
  refine exists_section_of_finite_lift A I a S.X₂ hinj ŝ W
    ((idealPowerMultiple K n
      (unitModule (complementZeroLocus A a : Scheme))).toSheafOfModules) p hp hker
    (idealPowerMultiple K n (unitModule (complementZeroLocus A a : Scheme))).ι
    (fun Z hZ => isIso_restrict_idealPowerMultiple_ι K n _ Z.openSet
      fun x hx => hsupp x (hZ hx).2)
    (fun i => S.f.val.app (op W.openSet) (S.X₁.presheaf.map
        (homOfLE (inf_le_left : W.openSet ≤ W₀.openSet)).op (t₀ i)) +
      (SheafOfModules.ιFree i ≫ m).val.app (op W.openSet)
        (1 : Γ((complementZeroLocus A a : Scheme), W.openSet)))
    fun i b => corrected_localSectionHom_π A I a S.f ŝ (l i)
      (SheafOfModules.ιFree i ≫ p ≫
        (idealPowerMultiple K n (unitModule (complementZeroLocus A a : Scheme))).ι)
      (SheafOfModules.ιFree i ≫ m) (hl i) W
      (S.X₁.presheaf.map (homOfLE (inf_le_left : W.openSet ≤ W₀.openSet)).op (t₀ i))
      ((comparisonMap_restrict_section A I a S.X₁ W₀ W inf_le_left (t₀ i)).trans (ht₀ i)) b

/-- **The middle comparison of Stacks 0H48**, in the packaged form
`Stacks.Algebraization.MiddleComparisonOfShortExact` used for Stacks 0EG2. -/
theorem middleComparisonOfShortExact : MiddleComparisonOfShortExact.{u} :=
  fun B _ _ J b T hT _ _ _ h₁ h₃ => isIso_comparisonMap_middle_of_ends B J b T hT h₁ h₃

end Stacks.Algebraization

end
