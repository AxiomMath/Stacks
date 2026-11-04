module

public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.Basic
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.StalkRingComparison
public import StacksFrontier.Homology.Tor.Independence
public import StacksFrontier.RingTheory.Tor.Balancing

/-!
# The multiplicity of a Tor sheaf at a point

Let `X` be a scheme and `ℱ`, `𝒢` two `𝒪_X`-modules. The multiplicity of the Tor sheaf
`Tor_p^{𝒪_X}(ℱ, 𝒢)` at a point `x` — the length of its stalk over the local ring, which is the
coefficient of the cycle `[Tor_p^{𝒪_X}(ℱ, 𝒢)]_k` at `x` — is the length of the Tor module
`Tor_p^{𝒪_{X, x}}(ℱ_x, 𝒢_x)` of the two stalks over `𝒪_{X, x}`.

The stalk of a Tor sheaf is the Tor module of the stalks by Tag 0AZT, but that comparison is
stated over the `RingCat`-valued stalk of the structure sheaf, the ring the module stalk functor
takes its values over, whereas a length read by `Stacks.Chow.sheafMultiplicity` is taken over the
`CommRingCat`-valued stalk `𝒪_{X, x}`. This file crosses between the two. The stalk is the same
abelian group for both rings and the two actions correspond under the comparison isomorphism of
the stalk rings, so the lengths agree; and restricting scalars along that isomorphism carries the
Tor module over one ring to the Tor module over the other.

## Main definitions

* `ModuleCat.restrictScalarsOfIso` — a module over one ring and the same abelian group over an
  isomorphic ring, with corresponding actions, agree after restriction of scalars.
* `AlgebraicGeometry.TorFormula.stalkModuleCat` — the stalk of an `𝒪_X`-module at `x` as a
  module over `𝒪_{X, x}`.

## Main results

* `Module.length_eq_of_smul_eq` — two module structures on one abelian group whose actions
  correspond under a ring isomorphism give the same length.
* `Module.length_restrictScalars_eq` and `Module.length_tor_restrictScalars_eq` — restriction of
  scalars along a ring isomorphism changes neither the length of a module nor the length of a
  Tor module.
* `Module.length_tor_comm` — the two Tor modules of a pair of modules have the same length.
* `AlgebraicGeometry.TorFormula.length_stalk_torSheaf_eq_length_tor_stalk` — the length over
  `𝒪_{X, x}` of the stalk of `Tor_p^{𝒪_X}(ℱ, 𝒢)` is the length of
  `Tor_p^{𝒪_{X, x}}(ℱ_x, 𝒢_x)`, and
  `AlgebraicGeometry.TorFormula.sheafMultiplicity_torSheaf_eq_length_tor_stalk` — the same for
  the multiplicity, which is that length truncated to a natural number.

## References

* [Stacks Project, Tag 0AZT](https://stacks.math.columbia.edu/tag/0AZT)
* [Stacks Project, Tag 02QX](https://stacks.math.columbia.edu/tag/02QX)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
* [Stacks Project, Tag 00M1](https://stacks.math.columbia.edu/tag/00M1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

/-- **Length is insensitive to a change of scalars along a ring isomorphism.** Two module
structures on one abelian group whose actions correspond under a ring isomorphism have
isomorphic submodule lattices, hence the same length. -/
theorem Module.length_eq_of_smul_eq {R S : Type u} [Ring R] [Ring S] (e : R ≃+* S)
    {M : Type u} [AddCommGroup M] [Module R M] [Module S M]
    (h : ∀ (r : R) (m : M), r • m = e r • m) :
    Module.length R M = Module.length S M := by
  let _ : RingHomInvPair (e : R →+* S) (e.symm : S →+* R) := RingHomInvPair.of_ringEquiv e
  let _ : RingHomInvPair (e.symm : S →+* R) (e : R →+* S) := RingHomInvPair.of_ringEquiv_symm e
  exact Module.length_eq_of_semilinearEquiv (σ := (e : R →+* S)) (τ := (e.symm : S →+* R))
    { toFun := id
      invFun := id
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := h }

/-- Restricting scalars along a ring isomorphism does not change the length. -/
theorem Module.length_restrictScalars_eq {R S : Type u} [Ring R] [Ring S] (e : R ≃+* S)
    (Z : ModuleCat.{u} S) :
    Module.length R ((ModuleCat.restrictScalars e.toRingHom).obj Z) = Module.length S Z := by
  let _ : Module S ((ModuleCat.restrictScalars e.toRingHom).obj Z) :=
    inferInstanceAs (Module S Z)
  exact Module.length_eq_of_smul_eq (M := ((ModuleCat.restrictScalars e.toRingHom).obj Z)) e
    (fun _ _ => rfl)

/-- A module over one ring and the same abelian group over an isomorphic ring, whose actions
correspond under the isomorphism, agree after restriction of scalars. -/
def ModuleCat.restrictScalarsOfIso {R S : Type u} [Ring R] [Ring S] (e : R ≃+* S)
    (Z : ModuleCat.{u} S) (W : ModuleCat.{u} R) (φ : (Z : Type u) ≃+ (W : Type u))
    (h : ∀ (r : R) (z : Z), φ (e r • z) = r • φ z) :
    (ModuleCat.restrictScalars e.toRingHom).obj Z ≅ W where
  hom := ModuleCat.ofHom (X := (ModuleCat.restrictScalars e.toRingHom).obj Z) (Y := W)
    { toFun := φ
      map_add' := fun a b => map_add φ a b
      map_smul' := h }
  inv := ModuleCat.ofHom (X := W) (Y := (ModuleCat.restrictScalars e.toRingHom).obj Z)
    { toFun := φ.symm
      map_add' := fun a b => map_add φ.symm a b
      map_smul' := fun r w => φ.injective (by
        exact (φ.apply_symm_apply (r • w)).trans
          (((h r (φ.symm w)).trans
            (congrArg (fun y => r • y) (φ.apply_symm_apply w))).symm)) }
  hom_inv_id := by ext z; exact φ.symm_apply_apply z
  inv_hom_id := by ext w; exact φ.apply_symm_apply w

/-- **Restricting scalars along a ring isomorphism does not change the length of a Tor
module.** -/
theorem Module.length_tor_restrictScalars_eq {R S : Type u} [CommRing R] [CommRing S]
    (e : R ≃+* S) (M N : ModuleCat.{u} S) (p : ℕ) :
    Module.length R
        (((Tor (ModuleCat.{u} R) p).obj
            ((ModuleCat.restrictScalars e.toRingHom).obj M)).obj
          ((ModuleCat.restrictScalars e.toRingHom).obj N))
      = Module.length S (((Tor (ModuleCat.{u} S) p).obj M).obj N) := by
  rw [(RingTheory.TorIndependence.torRestrictIso e M N p).toLinearEquiv.length_eq,
    Module.length_restrictScalars_eq]

/-- **The two Tor modules of a pair of modules have the same length**, by the balancing of `Tor`
through `Tor'` and the symmetry of the tensor product. -/
theorem Module.length_tor_comm {R : Type u} [CommRing R] (M N : ModuleCat.{u} R) (p : ℕ) :
    Module.length R (((Tor (ModuleCat.{u} R) p).obj M).obj N)
      = Module.length R (((Tor (ModuleCat.{u} R) p).obj N).obj M) :=
  (((Tor_iso_Tor' R p).app M).app N ≪≫
      (((torFlip_iso_Tor' R p).app M).app N).symm).toLinearEquiv.length_eq

namespace AlgebraicGeometry.TorFormula

/-- The stalk of an `𝒪_X`-module at a point, as a module over the local ring `𝒪_{X, x}`. -/
abbrev stalkModuleCat (X : Scheme.{u}) (F : X.Modules) (x : X) :
    ModuleCat.{u} (X.presheaf.stalk x) :=
  ModuleCat.of (X.presheaf.stalk x) (F.presheaf.stalk x)

/-- The two stalk rings act on the stalk of an `𝒪_X`-module through the comparison isomorphism,
so the stalk has the same length over both of them. -/
theorem length_stalkFunctor_obj_eq (X : Scheme.{u}) (F : X.Modules) (x : X) :
    Module.length (TopCat.Presheaf.stalk (C := RingCat.{u}) X.ringCatSheaf.obj x)
        ((Scheme.Modules.stalkFunctor X x).obj F)
      = Module.length (X.presheaf.stalk x) (F.presheaf.stalk x) := by
  let _ : Module (X.presheaf.stalk x) ((Scheme.Modules.stalkFunctor X x).obj F) :=
    inferInstanceAs (Module (X.presheaf.stalk x) (F.presheaf.stalk x))
  let _ : Module (ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf).obj x))
      ((Scheme.Modules.stalkFunctor X x).obj F) :=
    inferInstanceAs (Module (ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
      X.ringCatSheaf.obj x)) ((Scheme.Modules.stalkFunctor X x).obj F))
  exact Module.length_eq_of_smul_eq (M := ((Scheme.Modules.stalkFunctor X x).obj F))
    (stalkRingEquiv X x)
    (fun s m => (SemilinearStalk.comm_smul_eq X.presheaf x F.val s m).symm)

/-- **The multiplicity of a sheaf of modules at a point is the length of the value of the module
stalk functor there**, the length now read over the `RingCat`-valued stalk of the structure
sheaf. -/
theorem sheafMultiplicity_eq_length_stalkFunctor (X : Scheme.{u}) (F : X.Modules) (x : X) :
    Stacks.Chow.sheafMultiplicity F x =
      (Module.length (TopCat.Presheaf.stalk (C := RingCat.{u}) X.ringCatSheaf.obj x)
        ((Scheme.Modules.stalkFunctor X x).obj F)).toNat := by
  rw [length_stalkFunctor_obj_eq]
  rfl

/-- The value of the module stalk functor, read over `𝒪_{X, x}` by restricting scalars along the
comparison of the two stalk rings, is the stalk read over `𝒪_{X, x}` directly. -/
def stalkRestrictIso (X : Scheme.{u}) (F : X.Modules) (x : X) :
    (ModuleCat.restrictScalars (stalkRingEquiv X x).symm.toRingHom).obj
        ((Scheme.Modules.stalkFunctor X x).obj F) ≅
      stalkModuleCat X F x :=
  ModuleCat.restrictScalarsOfIso (stalkRingEquiv X x).symm
    ((Scheme.Modules.stalkFunctor X x).obj F) (stalkModuleCat X F x) (AddEquiv.refl _)
    (fun r m => by
      have h := SemilinearStalk.comm_smul_eq X.presheaf x F.val ((stalkRingEquiv X x).symm r) m
      rw [show SemilinearStalk.commStalkRingEquiv X.presheaf x ((stalkRingEquiv X x).symm r) = r
        from (stalkRingEquiv X x).apply_symm_apply r] at h
      exact h.symm)

/-- **The length of the stalk of a Tor sheaf is the length of the Tor module of the stalks.**
For `𝒪_X`-modules `ℱ`, `𝒢` and a point `x`, the length over `𝒪_{X, x}` of the stalk of
`Tor_p^{𝒪_X}(ℱ, 𝒢)` is the length of `Tor_p^{𝒪_{X, x}}(ℱ_x, 𝒢_x)`. This is what turns the
unnumbered "basic fact" opening Section 43.14 — the stalk clause of Tag 0AZT — into a statement
about the coefficients of the cycles of the Tor sheaves. -/
theorem length_stalk_torSheaf_eq_length_tor_stalk (X : Scheme.{u}) (F G : X.Modules)
    (p : ℕ) (x : X) :
    Module.length (X.presheaf.stalk x) ((torSheaf X F G p).presheaf.stalk x) =
      Module.length (X.presheaf.stalk x)
        (((Tor (ModuleCat.{u} (X.presheaf.stalk x)) p).obj (stalkModuleCat X F x)).obj
          (stalkModuleCat X G x)) := by
  let _ := StacksDraft.StalkTensor.commRing_stalk_ringSheaf X.sheaf x
  refine Eq.trans (length_stalkFunctor_obj_eq X (torSheaf X F G p) x).symm ?_
  refine Eq.trans (@LinearEquiv.length_eq _ _ _ _ _ _ _ (ModuleCat.isModule _)
    (torSheafStalkIso X F G p x).toLinearEquiv) ?_
  refine Eq.trans ((Module.length_tor_restrictScalars_eq (stalkRingEquiv X x).symm
    ((Scheme.Modules.stalkFunctor X x).obj F)
    ((Scheme.Modules.stalkFunctor X x).obj G) p).symm) ?_
  exact (((Tor (ModuleCat.{u} (X.presheaf.stalk x)) p).mapIso (stalkRestrictIso X F x)).app
      ((ModuleCat.restrictScalars (stalkRingEquiv X x).symm.toRingHom).obj
        ((Scheme.Modules.stalkFunctor X x).obj G)) ≪≫
    ((Tor (ModuleCat.{u} (X.presheaf.stalk x)) p).obj
      (stalkModuleCat X F x)).mapIso (stalkRestrictIso X G x)).toLinearEquiv.length_eq

/-- **The multiplicity of a Tor sheaf at a point is the length of the Tor module of the
stalks**, the multiplicity being that length truncated to a natural number. -/
theorem sheafMultiplicity_torSheaf_eq_length_tor_stalk (X : Scheme.{u}) (F G : X.Modules)
    (p : ℕ) (x : X) :
    Stacks.Chow.sheafMultiplicity (torSheaf X F G p) x =
      (Module.length (X.presheaf.stalk x)
        (((Tor (ModuleCat.{u} (X.presheaf.stalk x)) p).obj (stalkModuleCat X F x)).obj
          (stalkModuleCat X G x))).toNat :=
  congrArg (fun n : ℕ∞ => ((n.toNat : ℕ) : ℤ))
    (length_stalk_torSheaf_eq_length_tor_stalk X F G p x)

end AlgebraicGeometry.TorFormula

end
