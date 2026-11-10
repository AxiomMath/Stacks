module

public import StacksFrontier.AlgebraicGeometry.Duality.ProperOverField.Duality
public import StacksFrontier.AlgebraicGeometry.Duality.ProperOverField.DualizingModule

/-!
# Nonvanishing through the duality pairing

Let `X` be a proper scheme over a field `k` with relative dualizing complex `ω_X^•`, and let `𝒜`
be a quasi-coherent `𝒪_X`-module whose global sections `Γ(X, 𝒜)` form a one-dimensional
`k`-vector space. If `s : 𝒪_X ⟶ 𝒜` is nonzero on global sections, then for every nonzero
`α : 𝒜[0] ⟶ ω_X^•` in `D(𝒪_X)` the composite `s ≫ α : 𝒪_X[0] ⟶ ω_X^•` is nonzero.

This is the duality step of the proof of [Stacks, Tag 0G8E]: by part (5) of
[Stacks, Tag 0FVV] the linear form `H^0(X, 𝒜[0]) ⟶ k` attached to `s ≫ α` is the one attached to
`α` precomposed with `H^0(X, s)`; the latter form is nonzero on the one-dimensional space
`H^0(X, 𝒜[0]) = Γ(X, 𝒜)`, which `H^0(X, s)` meets nontrivially.

## Main results

* `Stacks.Duality.hypercohomologyZeroIsoGlobalSections`: `H^0(X, ℱ[0]) ≅ Γ(X, ℱ)` as `k`-vector
  spaces, naturally in `ℱ`.
* `Stacks.Duality.singleFunctor_map_comp_ne_zero`: the nonvanishing statement above.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Duality

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]

/-- The relative dualizing complex `ω_X^• = a(𝒪_{Spec k})` of `f : X ⟶ Spec k`. -/
local notation "ωX" =>
  relativeDualizingComplex f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
    (DerivedPushforward.derivedStructureSheaf (Spec (CommRingCat.of k)))

/-- **`H^0(X, ℱ[0]) ≅ Γ(X, ℱ)`**, as `k`-vector spaces and naturally in the module `ℱ`, the degree
being written `-0` as in part (5) of [Stacks, Tag 0FVV]. -/
def hypercohomologyZeroIsoGlobalSections :
    DerivedCategory.singleFunctor X.Modules 0 ⋙ derivedGlobalSectionsOver f ⋙
        DerivedCategory.homologyFunctor (ModuleCat k) (-(-((0 : ℕ) : ℤ))) ≅
      _root_.SheafOfModules.evaluation X.ringCatSheaf (op ⊤) ⋙
        ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ (by simp)).hom :=
  hypercohomologyNegNegIso f 0 ≪≫
    Functor.isoWhiskerRight
      (_root_.SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).rightDerivedZeroIsoSelf _

/-- **Nonvanishing through the duality pairing.** Let `𝒜` be quasi-coherent with `Γ(X, 𝒜)`
one-dimensional over `k`, let `s : 𝒪_X ⟶ 𝒜` be nonzero on global sections, and let
`α : 𝒜[0] ⟶ ω_X^•` be nonzero. Then `s[0] ≫ α ≠ 0`. -/
theorem singleFunctor_map_comp_ne_zero (A : X.Modules) [A.IsQuasicoherent]
    (hA : Module.finrank k ((ModuleCat.restrictScalars
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ (by simp)).hom).obj
        ((_root_.SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).obj A)) = 1)
    (s : _root_.SheafOfModules.unit X.ringCatSheaf ⟶ A)
    (hs : (A.unitHomEquiv s).val (op ⊤) ≠ 0)
    (α : (DerivedCategory.singleFunctor X.Modules 0).obj A ⟶ (ωX).obj⟦(0 : ℤ)⟧)
    (hα : α ≠ 0) :
    (DerivedCategory.singleFunctor X.Modules 0).map s ≫ α ≠ 0 := by
  intro h
  let := Scheme.linearOver f
  let KA := singleQuasiCoherentDegreeZero A
  let KO := singleQuasiCoherentDegreeZero (_root_.SheafOfModules.unit X.ringCatSheaf)
  let lamA := dualityEquiv f KA 0 α
  have hlam : lamA ≠ 0 := fun h' => hα ((dualityEquiv f KA 0).map_eq_zero_iff.1 h')
  let gD := (DerivedCategory.singleFunctor X.Modules 0).map s
  have hcomp : ∀ x, lamA ((DerivedCategory.homologyFunctor (ModuleCat k) (-0)).map
      ((derivedGlobalSectionsOver f).map gD) x) = 0 := fun x =>
    (dualityEquiv_comp f KO KA 0 gD α x).symm.trans
      ((congrArg (fun β => dualityEquiv f KO 0 β x) h).trans
        ((congrArg (fun φ => φ x) (dualityEquiv f KO 0).map_zero).trans (LinearMap.zero_apply x)))
  let e := hypercohomologyZeroIsoGlobalSections f
  have hV : Module.finrank k ((DerivedCategory.homologyFunctor (ModuleCat k) (-0)).obj
      ((derivedGlobalSectionsOver f).obj KA.obj)) = 1 :=
    (e.app A).toLinearEquiv.finrank_eq.trans hA
  let one : (_root_.SheafOfModules.evaluation X.ringCatSheaf (op ⊤) ⋙ ModuleCat.restrictScalars
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ (by simp)).hom).obj
        (_root_.SheafOfModules.unit X.ringCatSheaf) :=
    ((_root_.SheafOfModules.unit X.ringCatSheaf).unitHomEquiv (𝟙 _)).val (op ⊤)
  let v := (DerivedCategory.homologyFunctor (ModuleCat k) (-0)).map
    ((derivedGlobalSectionsOver f).map gD) ((e.app _).inv one)
  have hv : v ≠ 0 := by
    intro hv0
    apply hs
    have h2 : (e.app A).hom v = (A.unitHomEquiv s).val (op ⊤) := by
      change (e.app A).hom (((e.inv.app _) ≫ (DerivedCategory.singleFunctor X.Modules 0 ⋙
        derivedGlobalSectionsOver f ⋙ DerivedCategory.homologyFunctor (ModuleCat k)
          (-(-((0 : ℕ) : ℤ)))).map s) one) = _
      rw [← e.inv.naturality s]
      change (e.inv.app A ≫ e.hom.app A) _ = _
      rw [Iso.inv_hom_id_app]
      rfl
    rw [← h2, hv0]
    exact map_zero _
  apply hlam
  ext w
  obtain ⟨c, rfl⟩ := (finrank_eq_one_iff_of_nonzero' v hv).1 hV w
  exact (lamA.map_smul c v).trans ((congrArg (c • ·) (hcomp _)).trans (smul_zero c))

end Stacks.Duality
