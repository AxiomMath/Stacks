module

public import StacksFrontier.AlgebraicGeometry.DerivedGlobalSectionsLinear
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.ExtFinitenessLinear

/-!
# The base-field linear structure on modules over a scheme over a field

Let `X` be a scheme over a field `k`. This file records, at an arbitrary model of `D(𝒪_X)`, two
facts about the canonical `k`-linear structure `AlgebraicGeometry.modulesLinear`:

* `AlgebraicGeometry.smul_linearOver_eq_smul_modulesLinear`: it acts on `D(𝒪_X)` as
  `AlgebraicGeometry.Scheme.linearOver` does;
* `AlgebraicGeometry.restrictFunctor_linear` and
  `AlgebraicGeometry.mapDerivedCategory_restrictFunctor_linear`: restriction along an open
  immersion over the base is `k`-linear, on modules and on derived categories.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}} (q : X ⟶ Spec (CommRingCat.of k))

/-- The two `k`-linear structures on `𝒪_X`-modules have the same central endomorphisms. -/
theorem toCatCenter_linearOver_eq_modulesLinear (a : k) :
    @Linear.toCatCenter k _ X.Modules _ _ (Scheme.linearOver q) a =
      @Linear.toCatCenter k _ X.Modules _ _ (modulesLinear k (Over.mk q)) a := by
  refine CatCenter.ext _ _ fun M ↦ ?_
  ext U x
  rfl

/-- On `D(𝒪_X)`, `AlgebraicGeometry.Scheme.linearOver` and `AlgebraicGeometry.modulesLinear`
induce the same scalar action on morphisms of the derived category. -/
theorem smul_linearOver_eq_smul_modulesLinear [HasDerivedCategory X.Modules] (a : k)
    {Y Z : DerivedCategory X.Modules} (g : Y ⟶ Z) :
    (letI : Linear k X.Modules := Scheme.linearOver q; a • g) =
      (letI : Linear k X.Modules := modulesLinear k (Over.mk q); a • g) :=
  @smul_eq_of_toCatCenter_eq k k _ _ X.Modules _ _ _ (Scheme.linearOver q)
    (modulesLinear k (Over.mk q)) a a (toCatCenter_linearOver_eq_modulesLinear q a) Y Z g

/-! ### Restriction along an open immersion is `k`-linear -/

section Restrict

variable {U : Scheme.{u}} (p : U ⟶ Spec (CommRingCat.of k))
  (j : U ⟶ X) [IsOpenImmersion j] (h : j ≫ q = p)

include h in
/-- The image of a base scalar in the functions on an open `V` of `U`, carried to the functions on
`j(V)` along an open immersion `j : U ⟶ X` over the base, is the image of the scalar there. -/
theorem appIso_inv_baseRingToSections (V : U.Opens) (a : k) :
    (j.appIso V).inv.hom (baseRingToSections k (Over.mk p) (op V) a) =
      baseRingToSections k (Over.mk q) (op (j ''ᵁ V)) a := by
  have key : j.app ⊤ ≫ U.presheaf.map (homOfLE (show V ≤ j ⁻¹ᵁ ⊤ by simp)).op ≫
      (j.appIso V).inv = X.presheaf.map (homOfLE (show j ''ᵁ V ≤ ⊤ from le_top)).op := by
    rw [Scheme.Hom.appIso_inv_naturality, ← Category.assoc, Scheme.Hom.app_appIso_inv]
    exact (X.presheaf.map_comp _ _).symm.trans rfl
  subst h
  exact ConcreteCategory.congr_hom key (((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
    q.appTop).hom a)

include h in
/-- **Restriction along an open immersion over the base is `k`-linear**, for the canonical
`k`-linear structures `AlgebraicGeometry.modulesLinear` on both sides. -/
theorem restrictFunctor_linear :
    letI : Linear k X.Modules := modulesLinear k (Over.mk q)
    letI : Linear k U.Modules := modulesLinear k (Over.mk p)
    (Scheme.Modules.restrictFunctor j).Linear k := by
  let : Linear k X.Modules := modulesLinear k (Over.mk q)
  let : Linear k U.Modules := modulesLinear k (Over.mk p)
  refine ⟨fun {M N} g a ↦ ?_⟩
  ext V x
  exact (congrArg (fun r : X.ringCatSheaf.obj.obj (op (j ''ᵁ V)) ↦
    (g.val.app (op (j ''ᵁ V))).hom (r • (show M.val.obj (op (j ''ᵁ V)) from x)))
      (appIso_inv_baseRingToSections q p j h V a)).symm

include h in
/-- **The functor induced by restriction on derived categories is `k`-linear.** -/
theorem mapDerivedCategory_restrictFunctor_linear [HasDerivedCategory X.Modules]
    [HasDerivedCategory U.Modules] :
    letI : Linear k X.Modules := modulesLinear k (Over.mk q)
    letI : Linear k U.Modules := modulesLinear k (Over.mk p)
    (Scheme.Modules.restrictFunctor j).mapDerivedCategory.Linear k := by
  let : Linear k X.Modules := modulesLinear k (Over.mk q)
  let : Linear k U.Modules := modulesLinear k (Over.mk p)
  have := restrictFunctor_linear q p j h
  infer_instance

end Restrict

end AlgebraicGeometry

end
