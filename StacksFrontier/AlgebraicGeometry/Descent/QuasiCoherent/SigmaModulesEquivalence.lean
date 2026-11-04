module

public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.SigmaSummands
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.PushforwardVanishing
public import StacksFrontier.CategoryTheory.Pi.Preadditive
public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.Basic

/-!
# Sheaves of modules on a coproduct of schemes are the product over the summands

Let `Z : I → Scheme` be a family of schemes. Restriction to the summands,

  `(∐ Z).Modules ⥤ ∀ i, (Z i).Modules`,

is an **equivalence of categories**, for arbitrary (not necessarily quasi-coherent) sheaves of
modules and with no hypothesis on the family. A family of sheaves of modules on the summands
glues to one on `∐ Z` (Stacks 00AM applied to the summand charts, whose pairwise overlaps are
empty), and restriction to the summands is bijective on morphisms
(`AlgebraicGeometry.bijective_map_sigmaι`).

## Main definitions

* `AlgebraicGeometry.sigmaModulesGlueData`: the gluing datum on the summand charts of `∐ Z`
  built from a family of sheaves of modules on the summands. Its transitions are identities on
  the diagonal and the unique map between trivial modules off it.
* `AlgebraicGeometry.sigmaModulesFunctor`: restriction to the summands, as one functor
  `(∐ Z).Modules ⥤ ∀ i, (Z i).Modules`.
* `AlgebraicGeometry.sigmaModulesEquivalence`: **the equivalence**.

## Main results

* `AlgebraicGeometry.exists_restrict_iso_of_summandModules`: every family of sheaves of modules
  on the summands is the restriction of a sheaf of modules on `∐ Z`.
* `AlgebraicGeometry.sigmaModulesFunctor_essSurj`, and the `Full` and `Faithful` instances for
  `AlgebraicGeometry.sigmaModulesFunctor`.
* `AlgebraicGeometry.isIso_of_isIso_pullback_sigmaι`: a morphism of sheaves of modules on `∐ Z`
  whose restriction to each summand is invertible is invertible.

## References

* [Stacks Project, Tag 00AM](https://stacks.math.columbia.edu/tag/00AM)
* [Stacks Project, Tag 023E](https://stacks.math.columbia.edu/tag/023E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {I : Type u} (Z : I → Scheme.{u})

/-- The unique linear equivalence between two trivial modules. -/
def subsingletonLinearEquiv {R : Type*} [Ring R] {A B : Type*} [AddCommGroup A]
    [Module R A] [AddCommGroup B] [Module R B] [Subsingleton A] [Subsingleton B] :
    A ≃ₗ[R] B where
  toFun _ := 0
  map_add' _ _ := Subsingleton.elim _ _
  map_smul' _ _ := Subsingleton.elim _ _
  invFun _ := 0
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

/-- An open of `∐ Z` contained in the ranges of two distinct summands is empty. -/
theorem eq_bot_of_le_opensRange_sigmaι {i j : I} (hij : i ≠ j) {V : (∐ Z : Scheme.{u}).Opens}
    (hi : V ≤ (Sigma.ι Z i).opensRange) (hj : V ≤ (Sigma.ι Z j).opensRange) : V = ⊥ :=
  le_bot_iff.mp ((disjoint_opensRange_sigmaι Z i j hij).le_bot.trans' (le_inf hi hj))

/-- The sections over an empty open of the pushforward of a sheaf of modules on a summand are
trivial. -/
theorem subsingleton_openSections_of_eq_bot (M : ∀ i, (Z i).Modules) (i : I)
    {V : (∐ Z : Scheme.{u}).Opens} (hV : V = ⊥) :
    Subsingleton (Stacks.SheafOfModules.openSections (Sigma.ι Z i) (M i) V) :=
  RingedSpace.subsingleton_sections_of_eq_bot
    ((Scheme.Modules.pushforward (Sigma.ι Z i)).obj (M i)) hV

/-- The transition of `AlgebraicGeometry.sigmaModulesGlueData` on the diagonal: the identity,
transported along `i = j`. -/
def sigmaModulesTransDiag (M : ∀ i, (Z i).Modules) {i j : I} (h : i = j)
    (V : (∐ Z : Scheme.{u}).Opens) :
    Stacks.SheafOfModules.openSections (Sigma.ι Z i) (M i) V ≃ₗ[ToType
        ((∐ Z : Scheme.{u}).ringCatSheaf.obj.obj (op V))]
      Stacks.SheafOfModules.openSections (Sigma.ι Z j) (M j) V := by
  subst h
  exact LinearEquiv.refl _ _

/-- The transition of `AlgebraicGeometry.sigmaModulesGlueData`: the identity on the diagonal,
and off it the unique linear equivalence between the trivial modules of sections over an open
contained in the ranges of two distinct summands, which is empty. -/
def sigmaModulesTrans (M : ∀ i, (Z i).Modules) (i j : I)
    {V : (∐ Z : Scheme.{u}).Opens} (hi : V ≤ (Sigma.ι Z i).opensRange)
    (hj : V ≤ (Sigma.ι Z j).opensRange) :
    Stacks.SheafOfModules.openSections (Sigma.ι Z i) (M i) V ≃ₗ[ToType
        ((∐ Z : Scheme.{u}).ringCatSheaf.obj.obj (op V))]
      Stacks.SheafOfModules.openSections (Sigma.ι Z j) (M j) V :=
  letI := Classical.decEq I
  if h : i = j then sigmaModulesTransDiag Z M h V
  else
    have _ := subsingleton_openSections_of_eq_bot Z M i
      (eq_bot_of_le_opensRange_sigmaι Z h hi hj)
    have _ := subsingleton_openSections_of_eq_bot Z M j
      (eq_bot_of_le_opensRange_sigmaι Z h hi hj)
    subsingletonLinearEquiv

/-- On the diagonal, `AlgebraicGeometry.sigmaModulesTrans` is the identity. -/
theorem sigmaModulesTrans_self (M : ∀ i, (Z i).Modules) (i : I)
    {V : (∐ Z : Scheme.{u}).Opens} (hi hj : V ≤ (Sigma.ι Z i).opensRange) :
    sigmaModulesTrans Z M i i hi hj = LinearEquiv.refl _ _ := by
  rw [sigmaModulesTrans, dif_pos rfl]
  rfl

/-- The gluing datum on the summand charts of `∐ Z` given by a family of sheaves of modules on
the summands, with transitions `AlgebraicGeometry.sigmaModulesTrans`. -/
def sigmaModulesGlueData (M : ∀ i, (Z i).Modules) :
    Stacks.SheafOfModules.ModulesGlueData (∐ Z) (fun i => Sigma.ι Z i) where
  mod := M
  trans i j _ hi hj := sigmaModulesTrans Z M i j hi hj
  trans_map i j _ _ hi hj hWV s := by
    by_cases h : i = j
    · subst h
      simp only [sigmaModulesTrans_self]
      rfl
    · have _ := subsingleton_openSections_of_eq_bot Z M j
        (eq_bot_of_le_opensRange_sigmaι Z h (hWV.trans hi) (hWV.trans hj))
      exact Subsingleton.elim _ _
  trans_trans i j k _ hi hj hk s := by
    by_cases hij : i = j
    · subst hij
      by_cases hik : i = k
      · subst hik
        simp only [sigmaModulesTrans_self, LinearEquiv.refl_apply]
      · have _ := subsingleton_openSections_of_eq_bot Z M k
          (eq_bot_of_le_opensRange_sigmaι Z hik hi hk)
        exact Subsingleton.elim _ _
    · have _ := subsingleton_openSections_of_eq_bot Z M k
        (eq_bot_of_le_opensRange_sigmaι Z hij hi hj)
      exact Subsingleton.elim _ _

/-- Every family of sheaves of modules on the summands of `∐ Z` is the restriction of a sheaf
of modules on `∐ Z`. -/
theorem exists_restrict_iso_of_summandModules (M : ∀ i, (Z i).Modules) :
    ∃ N : (∐ Z : Scheme.{u}).Modules,
      ∀ i, Nonempty ((Scheme.Modules.pullback (Sigma.ι Z i)).obj N ≅ M i) :=
  ⟨(sigmaModulesGlueData Z M).glued, fun i =>
    ⟨(Scheme.Modules.restrictFunctorIsoPullback (Sigma.ι Z i)).symm.app _ ≪≫
      (sigmaModulesGlueData Z M).chartIso i⟩⟩

/-- **Restriction to the summands**, as one functor to the product of the categories of sheaves
of modules on the summands. -/
def sigmaModulesFunctor : (∐ Z : Scheme.{u}).Modules ⥤ ∀ i, (Z i).Modules :=
  Functor.pi' fun i => Scheme.Modules.pullback (Sigma.ι Z i)

/-- The component of `AlgebraicGeometry.sigmaModulesFunctor` at a summand `Z i` sends a sheaf of
modules to its pullback along `Sigma.ι Z i`. -/
@[simp]
theorem sigmaModulesFunctor_obj (N : (∐ Z : Scheme.{u}).Modules) (i : I) :
    (sigmaModulesFunctor Z).obj N i = (Scheme.Modules.pullback (Sigma.ι Z i)).obj N := rfl

/-- The component of `AlgebraicGeometry.sigmaModulesFunctor` at a summand `Z i` sends a morphism to
its pullback along `Sigma.ι Z i`. -/
@[simp]
theorem sigmaModulesFunctor_map {N N' : (∐ Z : Scheme.{u}).Modules} (φ : N ⟶ N') (i : I) :
    (sigmaModulesFunctor Z).map φ i = (Scheme.Modules.pullback (Sigma.ι Z i)).map φ := rfl

/-- Restriction to the summands is faithful. -/
instance sigmaModulesFunctor_faithful : (sigmaModulesFunctor Z).Faithful where
  map_injective {N N'} {_φ _ψ} h := injective_map_sigmaι N N' (funext fun k => congrFun h k)

/-- Restriction to the summands is full. -/
instance sigmaModulesFunctor_full : (sigmaModulesFunctor Z).Full where
  map_surjective {N N'} φ := (exists_hom_of_summandHoms N N' φ).imp fun _ h => funext h

/-- Restriction to the summands is essentially surjective. -/
instance sigmaModulesFunctor_essSurj : (sigmaModulesFunctor Z).EssSurj where
  mem_essImage M := by
    obtain ⟨N, hN⟩ := exists_restrict_iso_of_summandModules Z M
    exact ⟨N, ⟨Pi.isoMk fun i => (hN i).some⟩⟩

/-- Restriction to the summands is an equivalence. -/
instance sigmaModulesFunctor_isEquivalence : (sigmaModulesFunctor Z).IsEquivalence where

/-- **Sheaves of modules on a coproduct of schemes are the product over the summands.**
Restriction to the summands is an equivalence of categories

  `(∐ Z).Modules ≌ ∀ i, (Z i).Modules`,

for an arbitrary family of schemes and with no hypothesis on it. -/
def sigmaModulesEquivalence : (∐ Z : Scheme.{u}).Modules ≌ ∀ i, (Z i).Modules :=
  (sigmaModulesFunctor Z).asEquivalence

/-- **Invertibility of a morphism of sheaves of modules on a coproduct of schemes is detected on
the summands.** -/
theorem isIso_of_isIso_pullback_sigmaι {N N' : (∐ Z : Scheme.{u}).Modules} (φ : N ⟶ N')
    (h : ∀ i, IsIso ((Scheme.Modules.pullback (Sigma.ι Z i)).map φ)) : IsIso φ := by
  have : IsIso ((sigmaModulesFunctor Z).map φ) := by rwa [isIso_pi_iff]
  exact isIso_of_reflects_iso φ (sigmaModulesFunctor Z)

end AlgebraicGeometry

end
