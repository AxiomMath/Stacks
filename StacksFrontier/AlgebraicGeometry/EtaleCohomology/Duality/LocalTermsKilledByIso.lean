module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.BoundaryLocalTerms
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.AbelianShriekPresentation

/-!
# The bound on the local terms is invariant under isomorphism

`Stacks.EtaleCohomology.LAdicSheaf.LocalTermsKilledBy F K` says that `ℓ ^ K` kills the cokernel of
`j'_! Fₙ ⟶ j'_* Fₙ` and `R¹j'_* Fₙ` at every level. Both are functors of the level `Fₙ`, so the
property transfers along an isomorphism of ℓ-adic sheaves
(`Stacks.EtaleCohomology.LAdicSheaf.LocalTermsKilledBy.of_iso`); this moves the bound obtained
at the geometric generic point to the sheaf built at another base point, for Poincaré duality on
the fibres of the Fourier family ([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)).

## Main results

* `Stacks.EtaleCohomology.LAdicSheaf.LocalTermsKilledBy.of_iso`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale
  Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize

variable {B : BigEtaleSite.{u}} {U : B.Scheme} {ℓ : ℕ}
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B U.1 U.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian U.1] [Fact ℓ.Prime]
  {k : Type u} [Field k] {f : U.1 ⟶ Spec (.of k)} {j : CompactificationOf (Over.mk f)}
  {kbar : Type u} [Field kbar] [Algebra k kbar]

/-- The level `Fₙ ≅ Gₙ` of an isomorphism of ℓ-adic sheaves, on Mathlib's small étale site. -/
def LAdicSheaf.etaleLevelIso {F G : LAdicSheaf.{u, u + 1} B U ℓ} (e : F ≅ G) (n : ℕ) :
    LAdicSheaf.etaleLevel B U ℓ F n ≅ LAdicSheaf.etaleLevel B U ℓ G n :=
  (SmallEtale.sheafEquiv B U.1 U.property (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).functor.mapIso
    { hom := e.hom.app n
      inv := e.inv.app n
      hom_inv_id := congrArg (fun φ : F ⟶ F => φ.app n) e.hom_inv_id
      inv_hom_id := congrArg (fun φ : G ⟶ G => φ.app n) e.inv_hom_id }

/-- **The bound on the local terms at the boundary transfers along isomorphisms.** -/
theorem LAdicSheaf.LocalTermsKilledBy.of_iso {F G : LAdicSheaf.{u, u + 1} B U ℓ} (e : F ≅ G) {K : ℕ}
    (h : LAdicSheaf.LocalTermsKilledBy B U ℓ f j kbar F K) :
    LAdicSheaf.LocalTermsKilledBy B U ℓ f j kbar G K := by
  intro n
  obtain ⟨h₁, h₂⟩ := h n
  let eₙ := (etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
    (fieldBaseChangeProj (Over.mk f) kbar)).mapIso (LAdicSheaf.etaleLevelIso e n)
  refine ⟨CategoryTheory.nsmul_id_eq_zero_of_iso (cokernel.mapIso _ _
    ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1)))
      (fieldBaseChangeMap j.obj.hom kbar)).mapIso eₙ)
    ((etaleModuleDirectImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
      (fieldBaseChangeMap j.obj.hom kbar)).mapIso eₙ)
    ((etaleModuleExtensionByZeroToDirectImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
      (fieldBaseChangeMap j.obj.hom kbar)).naturality eₙ.hom).symm) _ h₁,
    CategoryTheory.nsmul_id_eq_zero_of_iso
      (((etaleModuleDirectImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
        (fieldBaseChangeMap j.obj.hom kbar)).rightDerived 1).mapIso eₙ) _ h₂⟩

end Stacks.EtaleCohomology

end
