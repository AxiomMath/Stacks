module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeSheafStalkBasis
public import StacksFrontier.AlgebraicGeometry.Modules.FreeSections
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.FittingIdealFreeModelRestrict

/-!
# The chosen bases of a finite free model, and their restriction to a smaller open

`AlgebraicGeometry.DerivedFreeModel K U` records a bounded-above finite free model, over the open
`U`, of a complex `K` of `𝒪_X`-modules, and `AlgebraicGeometry.DerivedFreeModel.matrix` reads the
matrix of its differential in the chosen bases of its sections over `U`. The Fitting ideal sheaf of
[Stacks, Tag 0ESP] is `Scheme.IdealSheafData.ofIdeals` applied to the family of ideals of minors of
all such models, so a *lower* bound on it needs to know how that family behaves on passing from `U`
to a smaller open, hence a model over the smaller open built from one over `U`.

Two of the four fields of such a restriction are in
`StacksFrontier.AlgebraicGeometry.PseudoCoherent.FittingIdealFreeModelRestrict`. This file supplies
the remaining one, the `basis` field, and with it the comparison of the two matrices: the matrix
of `d_p` over the smaller open is the *entrywise image* of the matrix over `U`.

The chosen basis of a model is arbitrary data, so the restricted basis cannot be read off it: the
restriction of an arbitrary basis of `Γ(N, U)` need not be a basis of `Γ(N, V)`. What makes it one
is the trivialization recorded by the `isFree` field. The route is therefore: the *tautological*
basis of the sections of a finite free sheaf of modules is natural under restriction
(`Stacks.SheafOfModules.freeSheafBasis_natural`), so a trivialization over `U` produces a pair of
bases, one over `U` and one over `V`, matched by the restriction maps; and the image of *any*
basis under a semilinear map matching one basis with another is again a basis, because it differs
from the matched one by the base change of an invertible change-of-basis matrix. That image is
then the restricted basis, and its vectors are literally the restrictions of the given ones, so
the matrices compare entry by entry.

## Main definitions

* `Stacks.basisOfSemilinear`: a basis transported along an additive isomorphism which is
  semilinear over a ring isomorphism.
* `Stacks.basisOfSemilinearImage`: the image of a basis under a semilinear map carrying one basis
  onto another.
* `AlgebraicGeometry.Scheme.Modules.freeBasis`: the tautological basis of the sections of a finite
  free `𝒪_Y`-module over an open, in the scheme spelling of
  `AlgebraicGeometry.Scheme.Modules.free`.
* `AlgebraicGeometry.Scheme.Modules.basisOfIsoFree`: its image under a trivialization.
* `AlgebraicGeometry.Scheme.Modules.crossBasis`: a basis of the sections of a restricted module,
  read on the ambient scheme.

## Main results

* `Stacks.basisOfSemilinearImage_apply` and `Stacks.basisOfSemilinearImage_repr`: the vectors of
  the image basis are the images of the given vectors, and the coordinates in it of an image are
  the images of the coordinates.
* `AlgebraicGeometry.Scheme.Modules.exists_basis_pair_of_isoFree`: a trivialization of a module
  over `U` produces, for nested opens of `U`, a pair of bases of the sections matched by the
  restriction maps of the ambient scheme.
* `AlgebraicGeometry.DerivedFreeModel.exists_basis_pair`: that pair for one degree of a finite free
  model, read at `U` and at any `V ≤ U`.
* `AlgebraicGeometry.DerivedFreeModel.toMatrix_eq_matrix_map`: a family of bases over `V` whose
  coordinates are the images of the coordinates over `U` computes the matrix of `d_p` as the
  entrywise image of `AlgebraicGeometry.DerivedFreeModel.matrix`.

## Implementation notes

The sections of the restriction of `N` to `U` over an open `W` of `U` and the sections of `N` over
`U.ι ''ᵁ W` are the same type, by `AlgebraicGeometry.Scheme.Modules.restrict_obj`, but the module
structures are *not* interchangeable to the elaborator: the scalar action of the restriction goes
through `AlgebraicGeometry.Scheme.Hom.appIso`, and although that isomorphism is the identity for
`U.ι` by `AlgebraicGeometry.Scheme.Opens.ι_appIso`, instance search and definitional unfolding do
not see it. `AlgebraicGeometry.Scheme.Modules.crossBasis` therefore crosses the boundary through
`Stacks.basisOfSemilinear` applied to `AlgebraicGeometry.Scheme.Modules.restrictAppIso` and that
`appIso`, which is exactly the semilinearity recorded by
`AlgebraicGeometry.Scheme.Modules.smul_restrictAppIso_hom`.

The opens are passed to `AlgebraicGeometry.Scheme.Modules.exists_basis_pair_of_isoFree` as opens
`W' ≤ W` of `U` *together with* equations naming their images in `X`, so that the caller supplies
`U.ι ''ᵁ ⊤ = U` and `U.ι ''ᵁ (U.ι ⁻¹ᵁ V) = V` and the proof substitutes them away; this avoids
transporting a basis along an equality of opens.

## References

* [Stacks Project, Tag 0ESP](https://stacks.math.columbia.edu/tag/0ESP)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite

namespace Stacks

universe u

/-! ### Two transports of a basis -/

section Semilinear

variable {R S : Type*} [CommRing R] [CommRing S] {M N : Type*}
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N] {ι : Type*}

/-- The coordinate isomorphism of a basis read through a semilinear additive isomorphism. -/
noncomputable def basisEquivFunOfSemilinear [Fintype ι] (φ : R ≃+* S) (ρ : M ≃+ N)
    (hρ : ∀ (r : R) (x : M), ρ (r • x) = φ r • ρ x) (b : Module.Basis ι R M) :
    N ≃ₗ[S] ι → S where
  toFun y k := φ (b.equivFun (ρ.symm y) k)
  invFun c := ρ (b.equivFun.symm fun k => φ.symm (c k))
  map_add' y z := by
    funext k
    simp only [map_add, Pi.add_apply]
  map_smul' s y := by
    have hsymm : ρ.symm (s • y) = φ.symm s • ρ.symm y := by
      refine ρ.injective ?_
      rw [ρ.apply_symm_apply, hρ, φ.apply_symm_apply, ρ.apply_symm_apply]
    funext k
    simp only [hsymm, map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [map_mul, φ.apply_symm_apply]
  left_inv y := by
    simp only [φ.symm_apply_apply]
    rw [show (fun k => b.equivFun (ρ.symm y) k) = b.equivFun (ρ.symm y) from rfl,
      LinearEquiv.symm_apply_apply, ρ.apply_symm_apply]
  right_inv c := by
    funext k
    change φ (b.equivFun (ρ.symm (ρ (b.equivFun.symm fun j => φ.symm (c j)))) k) = c k
    rw [ρ.symm_apply_apply, LinearEquiv.apply_symm_apply, φ.apply_symm_apply]

/-- **A basis transported along a semilinear additive isomorphism.** If `ρ : M ≃+ N` is additive
and semilinear over a ring isomorphism `φ : R ≃+* S`, then the image under `ρ` of a basis of `M`
over `R` is a basis of `N` over `S`. -/
noncomputable def basisOfSemilinear [Fintype ι] [DecidableEq ι] (φ : R ≃+* S) (ρ : M ≃+ N)
    (hρ : ∀ (r : R) (x : M), ρ (r • x) = φ r • ρ x) (b : Module.Basis ι R M) :
    Module.Basis ι S N :=
  Module.Basis.ofEquivFun (basisEquivFunOfSemilinear φ ρ hρ b)

/-- The `k`-th vector of the transported basis is the image under `ρ` of the `k`-th vector of
`b`. -/
@[simp]
theorem basisOfSemilinear_apply [Fintype ι] [DecidableEq ι] (φ : R ≃+* S) (ρ : M ≃+ N)
    (hρ : ∀ (r : R) (x : M), ρ (r • x) = φ r • ρ x) (b : Module.Basis ι R M) (k : ι) :
    basisOfSemilinear φ ρ hρ b k = ρ (b k) := by
  have hsingle : (fun j => φ.symm ((Pi.single k 1 : ι → S) j)) = (Pi.single k 1 : ι → R) := by
    funext j
    by_cases h : j = k
    · subst h
      rw [Pi.single_eq_same, Pi.single_eq_same, map_one]
    · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, map_zero]
  rw [basisOfSemilinear, Module.Basis.coe_ofEquivFun]
  change ρ (b.equivFun.symm fun j => φ.symm ((Pi.single k 1 : ι → S) j)) = ρ (b k)
  rw [hsingle]
  refine congrArg ρ ?_
  conv_rhs => rw [← Module.Basis.ofEquivFun_equivFun b]
  rw [Module.Basis.coe_ofEquivFun]

end Semilinear

section SemilinearImage

variable {R S : Type*} [CommRing R] [CommRing S] {M N : Type*}
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N] {ι : Type*}

open Matrix

/-- A semilinear additive map sends `x` to the combination, with the images of its coordinates in
`b`, of any family matched with `b` by the map. -/
private theorem semilinear_apply_eq_sum_repr [Fintype ι] (φ : R →+* S) (ρ : M →+ N)
    (hρ : ∀ (r : R) (x : M), ρ (r • x) = φ r • ρ x) (b : Module.Basis ι R M) (w : ι → N)
    (hw : ∀ k, ρ (b k) = w k) (x : M) : ρ x = ∑ i, φ (b.repr x i) • w i := by
  conv_lhs => rw [← b.sum_repr x]
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [hρ, hw i]

/-- **The image of any basis under a semilinear map carrying one basis onto another is again a
basis.** The hypothesis is a *pair* of bases matched by `ρ`: the image of an arbitrary basis `b`
differs from `f` by the base change along `φ` of the change-of-basis matrix from `e` to `b`,
which is invertible because that matrix is. -/
noncomputable def basisOfSemilinearImage [Fintype ι] [DecidableEq ι] (φ : R →+* S)
    (e : Module.Basis ι R M) (f : Module.Basis ι S N) (b : Module.Basis ι R M) :
    Module.Basis ι S N :=
  f.map (Matrix.toLinearEquiv f ((e.toMatrix b).map φ)
    (by
      have : Invertible (e.toMatrix b) := Module.Basis.invertibleToMatrix e b
      have hd : ((e.toMatrix b).map φ).det = φ ((e.toMatrix b).det) :=
        (RingHom.map_det φ (e.toMatrix b)).symm
      rw [hd]
      exact (Matrix.isUnit_det_of_invertible (e.toMatrix b)).map φ))

/-- The `k`-th vector of the image basis is the image under `ρ` of the `k`-th vector of `b`. -/
@[simp]
theorem basisOfSemilinearImage_apply [Fintype ι] [DecidableEq ι] (φ : R →+* S) (ρ : M →+ N)
    (hρ : ∀ (r : R) (x : M), ρ (r • x) = φ r • ρ x) (e : Module.Basis ι R M)
    (f : Module.Basis ι S N) (hef : ∀ k, ρ (e k) = f k) (b : Module.Basis ι R M) (k : ι) :
    basisOfSemilinearImage φ e f b k = ρ (b k) := by
  rw [semilinear_apply_eq_sum_repr φ ρ hρ e f hef (b k),
    basisOfSemilinearImage, Module.Basis.map_apply, Matrix.toLinearEquiv_apply,
    Matrix.toLin_self]
  exact Finset.sum_congr rfl fun i _ => rfl

/-- The coordinates of the image of a vector under `ρ`, in the image basis, are the images of
its coordinates in `b`. -/
theorem basisOfSemilinearImage_repr [Fintype ι] [DecidableEq ι] (φ : R →+* S) (ρ : M →+ N)
    (hρ : ∀ (r : R) (x : M), ρ (r • x) = φ r • ρ x) (e : Module.Basis ι R M)
    (f : Module.Basis ι S N) (hef : ∀ k, ρ (e k) = f k) (b : Module.Basis ι R M) (x : M)
    (j : ι) :
    (basisOfSemilinearImage φ e f b).repr (ρ x) j = φ (b.repr x j) := by
  rw [semilinear_apply_eq_sum_repr φ ρ hρ b _
    (fun k => (basisOfSemilinearImage_apply φ ρ hρ e f hef b k).symm) x, Module.Basis.repr_sum_self]

end SemilinearImage

end Stacks

/-! ### The tautological basis of the sections of a finite free `𝒪_X`-module -/

namespace AlgebraicGeometry

open scoped AlgebraicGeometry

universe u

/-- **The tautological basis of the sections of a finite free `𝒪_Y`-module over an open.** -/
noncomputable def Scheme.Modules.freeBasis {Y : Scheme.{u}} (ι : Type u) [Fintype ι]
    [DecidableEq ι] (W : Y.Opens) :
    Module.Basis ι Γ(Y, W) Γ(Scheme.Modules.free Y ι, W) :=
  Stacks.SheafOfModules.freeSheafBasis (Osharp := Y.sheaf) W

/-- The tautological basis is natural: restriction carries the `k`-th vector to the `k`-th
vector. -/
theorem Scheme.Modules.freeBasis_natural {Y : Scheme.{u}} (ι : Type u) [Fintype ι]
    [DecidableEq ι] {W W' : Y.Opens} (h : W' ≤ W) (k : ι) :
    (Scheme.Modules.free Y ι).presheaf.map (homOfLE h).op
        (Scheme.Modules.freeBasis ι W k) = Scheme.Modules.freeBasis ι W' k :=
  Stacks.SheafOfModules.freeSheafBasis_natural (Osharp := Y.sheaf) h k

/-- The sections over an open of an isomorphism of `𝒪_Y`-modules, as a linear equivalence. -/
noncomputable def Scheme.Modules.appLinearEquiv {Y : Scheme.{u}} {M N : Y.Modules} (e : M ≅ N)
    (W : Y.Opens) : Γ(M, W) ≃ₗ[Γ(Y, W)] Γ(N, W) :=
  LinearEquiv.ofBijective
    { toFun := e.hom.app W
      map_add' := map_add _
      map_smul' := Scheme.Modules.Hom.app_smul e.hom }
    (ConcreteCategory.bijective_of_isIso (e.hom.app W))

/-- The linear equivalence on sections acts as the component of `e` over `W`. -/
@[simp]
theorem Scheme.Modules.appLinearEquiv_apply {Y : Scheme.{u}} {M N : Y.Modules} (e : M ≅ N)
    (W : Y.Opens) (x : Γ(M, W)) :
    Scheme.Modules.appLinearEquiv e W x = e.hom.app W x := rfl

/-- The naturality of the action on sections of a morphism of `𝒪_Y`-modules. -/
theorem Scheme.Modules.map_app {Y : Scheme.{u}} {M N : Y.Modules} (f : M ⟶ N)
    {W W' : Y.Opens} (h : W' ≤ W) (x : Γ(M, W)) :
    N.presheaf.map (homOfLE h).op (f.app W x) =
      f.app W' (M.presheaf.map (homOfLE h).op x) :=
  congr($(f.mapPresheaf.naturality (homOfLE h).op) x).symm

/-- **The basis of the sections of a trivialized `𝒪_Y`-module over an open**: the image of the
tautological basis under the trivialization. -/
noncomputable def Scheme.Modules.basisOfIsoFree {Y : Scheme.{u}} {N : Y.Modules} {ι : Type u}
    [Fintype ι] [DecidableEq ι] (e : N ≅ Scheme.Modules.free Y ι) (W : Y.Opens) :
    Module.Basis ι Γ(Y, W) Γ(N, W) :=
  (Scheme.Modules.freeBasis ι W).map (Scheme.Modules.appLinearEquiv e.symm W)

/-- `AlgebraicGeometry.Scheme.Modules.basisOfIsoFree` is natural under restriction. -/
theorem Scheme.Modules.basisOfIsoFree_natural {Y : Scheme.{u}} {N : Y.Modules} {ι : Type u}
    [Fintype ι] [DecidableEq ι] (e : N ≅ Scheme.Modules.free Y ι) {W W' : Y.Opens}
    (h : W' ≤ W) (k : ι) :
    N.presheaf.map (homOfLE h).op (Scheme.Modules.basisOfIsoFree e W k) =
      Scheme.Modules.basisOfIsoFree e W' k := by
  change N.presheaf.map (homOfLE h).op (e.inv.app W (Scheme.Modules.freeBasis ι W k)) =
    e.inv.app W' (Scheme.Modules.freeBasis ι W' k)
  rw [Scheme.Modules.map_app e.inv h, Scheme.Modules.freeBasis_natural ι h]

/-! ### Crossing the restriction boundary -/

/-- The ring isomorphism between the sections of `𝒪_X` over `U.ι ''ᵁ W` and the sections of the
structure sheaf of `U` over `W`, read in the direction the scalar action on the sections of a
restricted module uses. -/
noncomputable def Scheme.Modules.crossRingEquiv {X : Scheme.{u}} (U : X.Opens)
    (W : U.toScheme.Opens) : Γ(U.toScheme, W) ≃+* Γ(X, U.ι ''ᵁ W) :=
  (U.ι.appIso W).symm.commRingCatIsoToRingEquiv

/-- The additive isomorphism identifying the sections over `W` of the restriction of `N₀` to `U`
with the sections of `N₀` over `U.ι ''ᵁ W`. -/
noncomputable def Scheme.Modules.crossAddEquiv {X : Scheme.{u}} (N₀ : X.Modules) (U : X.Opens)
    (W : U.toScheme.Opens) :
    Γ((Scheme.Modules.restrictFunctor U.ι).obj N₀, W) ≃+ Γ(N₀, U.ι ''ᵁ W) :=
  (Scheme.Modules.restrictAppIso U.ι N₀ W).addCommGroupIsoToAddEquiv

/-- The additive isomorphism `Scheme.Modules.crossAddEquiv` is semilinear over
`Scheme.Modules.crossRingEquiv`. -/
theorem Scheme.Modules.crossAddEquiv_smul {X : Scheme.{u}} (N₀ : X.Modules) (U : X.Opens)
    (W : U.toScheme.Opens) (r : Γ(U.toScheme, W))
    (x : Γ((Scheme.Modules.restrictFunctor U.ι).obj N₀, W)) :
    Scheme.Modules.crossAddEquiv N₀ U W (r • x) =
      Scheme.Modules.crossRingEquiv U W r • Scheme.Modules.crossAddEquiv N₀ U W x :=
  Scheme.Modules.smul_restrictAppIso_hom_apply U.ι N₀ W r x

/-- **A basis of the sections of a restricted module, read on the ambient scheme.** -/
noncomputable def Scheme.Modules.crossBasis {X : Scheme.{u}} (N₀ : X.Modules) (U : X.Opens)
    (W : U.toScheme.Opens) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : Module.Basis ι Γ(U.toScheme, W)
      Γ((Scheme.Modules.restrictFunctor U.ι).obj N₀, W)) :
    Module.Basis ι Γ(X, U.ι ''ᵁ W) Γ(N₀, U.ι ''ᵁ W) :=
  Stacks.basisOfSemilinear (Scheme.Modules.crossRingEquiv U W)
    (Scheme.Modules.crossAddEquiv N₀ U W)
    (Scheme.Modules.crossAddEquiv_smul N₀ U W) g

/-- The `k`-th vector of the crossed basis is the image of the `k`-th vector of `g` under
`Scheme.Modules.crossAddEquiv`. -/
@[simp]
theorem Scheme.Modules.crossBasis_apply {X : Scheme.{u}} (N₀ : X.Modules) (U : X.Opens)
    (W : U.toScheme.Opens) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : Module.Basis ι Γ(U.toScheme, W)
      Γ((Scheme.Modules.restrictFunctor U.ι).obj N₀, W)) (k : ι) :
    Scheme.Modules.crossBasis N₀ U W g k =
      Scheme.Modules.crossAddEquiv N₀ U W (g k) :=
  Stacks.basisOfSemilinear_apply _ _ _ g k

/-- The crossed basis is natural under restriction, for the restriction maps of the ambient
scheme. -/
theorem Scheme.Modules.crossBasis_natural {X : Scheme.{u}} {N₀ : X.Modules} {U : X.Opens}
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (e : (Scheme.Modules.restrictFunctor U.ι).obj N₀ ≅ Scheme.Modules.free U.toScheme ι)
    {W W' : U.toScheme.Opens} (hW : W' ≤ W)
    (hBA : U.ι ''ᵁ W' ≤ U.ι ''ᵁ W) (k : ι) :
    N₀.presheaf.map (homOfLE hBA).op
        (Scheme.Modules.crossBasis N₀ U W (Scheme.Modules.basisOfIsoFree e W) k) =
      Scheme.Modules.crossBasis N₀ U W' (Scheme.Modules.basisOfIsoFree e W') k := by
  rw [Scheme.Modules.crossBasis_apply, Scheme.Modules.crossBasis_apply,
    ← Scheme.Modules.basisOfIsoFree_natural e hW k]
  change N₀.presheaf.map (homOfLE hBA).op
      ((Scheme.Modules.restrictAppIso U.ι N₀ W).hom
        (Scheme.Modules.basisOfIsoFree e W k)) =
    (Scheme.Modules.restrictAppIso U.ι N₀ W').hom
      (((Scheme.Modules.restrictFunctor U.ι).obj N₀).presheaf.map (homOfLE hW).op
        (Scheme.Modules.basisOfIsoFree e W k))
  rw [Scheme.Modules.map_restrictAppIso_hom_apply U.ι N₀ (homOfLE hW).op]

/-- **The pair of bases that a trivialization over `U` provides on two nested opens**, matched by
the restriction maps of the ambient scheme: the image under restriction of the `k`-th vector over
the larger open is the `k`-th vector over the smaller one.

The two opens are given as opens `W' ≤ W` of `U` together with equations identifying their images
in `X`, so that the statement can be read at `U` itself and at any `V ≤ U`. -/
theorem Scheme.Modules.exists_basis_pair_of_isoFree {X : Scheme.{u}} (N₀ : X.Modules)
    (U : X.Opens) {n : ℕ}
    (hfree : Nonempty ((Scheme.Modules.restrictFunctor U.ι).obj N₀ ≅
      Scheme.Modules.free U.toScheme (ULift.{u} (Fin n))))
    {W W' : U.toScheme.Opens} (hW : W' ≤ W) (A B : X.Opens)
    (hA : U.ι ''ᵁ W = A) (hB : U.ι ''ᵁ W' = B) (hBA : B ≤ A) :
    ∃ (g : Module.Basis (Fin n) Γ(X, A) Γ(N₀, A))
      (g' : Module.Basis (Fin n) Γ(X, B) Γ(N₀, B)),
      ∀ k, N₀.presheaf.map (homOfLE hBA).op (g k) = g' k := by
  obtain ⟨e⟩ := hfree
  subst hA
  subst hB
  refine ⟨(Scheme.Modules.crossBasis N₀ U W
      (Scheme.Modules.basisOfIsoFree e W)).reindex (Equiv.ulift (α := Fin n)),
    (Scheme.Modules.crossBasis N₀ U W'
      (Scheme.Modules.basisOfIsoFree e W')).reindex (Equiv.ulift (α := Fin n)), fun k => ?_⟩
  rw [Module.Basis.reindex_apply, Module.Basis.reindex_apply]
  exact Scheme.Modules.crossBasis_natural e hW hBA _

/-! ### The restriction of a finite free model -/

/-- Restriction of sections of an `𝒪_X`-module, as an additive map. -/
noncomputable def Scheme.Modules.resAddHom {X : Scheme.{u}} (N : X.Modules) {V W : X.Opens}
    (h : V ≤ W) : Γ(N, W) →+ Γ(N, V) :=
  (N.presheaf.map (homOfLE h).op).hom

/-- The additive restriction map acts as the restriction map of the presheaf of `N`. -/
@[simp]
theorem Scheme.Modules.resAddHom_apply {X : Scheme.{u}} (N : X.Modules) {V W : X.Opens}
    (h : V ≤ W) (x : Γ(N, W)) :
    Scheme.Modules.resAddHom N h x = N.presheaf.map (homOfLE h).op x := rfl

/-- Restriction of sections is semilinear over the restriction map of the structure sheaf. -/
theorem Scheme.Modules.resAddHom_smul {X : Scheme.{u}} (N : X.Modules) {V W : X.Opens}
    (h : V ≤ W) (r : Γ(X, W)) (x : Γ(N, W)) :
    Scheme.Modules.resAddHom N h (r • x) =
      (X.presheaf.map (homOfLE h).op).hom r • Scheme.Modules.resAddHom N h x :=
  Scheme.Modules.map_smul N (homOfLE h) r x

namespace DerivedFreeModel

variable {X : Scheme.{u}} {K : CochainComplex X.Modules ℤ} {U : X.Opens}

/-- **The pair of bases of the sections of a finite free model in one degree**, over `U` and over
a smaller open `V`, matched by the restriction maps. -/
theorem exists_basis_pair (M : DerivedFreeModel K U) {V : X.Opens} (hVU : V ≤ U) (i : ℤ) :
    ∃ (g : Module.Basis (Fin (M.rank i)) Γ(X, U) Γ(M.model.X i, U))
      (g' : Module.Basis (Fin (M.rank i)) Γ(X, V) Γ(M.model.X i, V)),
      ∀ k, (M.model.X i).presheaf.map (homOfLE hVU).op (g k) = g' k :=
  Scheme.Modules.exists_basis_pair_of_isoFree (M.model.X i) U (M.isFree i)
    (W := ⊤) (W' := U.ι ⁻¹ᵁ V) le_top U V U.ι_image_top
    (by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
      exact inf_eq_right.mpr hVU)
    hVU

/-- **The matrix of the differential in a restricted pair of bases is the entrywise image of its
matrix over the larger open.** -/
theorem toMatrix_eq_matrix_map (M : DerivedFreeModel K U) {V : X.Opens} (hVU : V ≤ U)
    (c : ∀ i : ℤ, Module.Basis (Fin (M.rank i)) Γ(X, V) Γ(M.model.X i, V))
    (hc : ∀ (i : ℤ) (x : Γ(M.model.X i, U)) (j : Fin (M.rank i)),
      (c i).repr ((M.model.X i).presheaf.map (homOfLE hVU).op x) j =
        (X.presheaf.map (homOfLE hVU).op).hom ((M.basis i).repr x j))
    (hc' : ∀ (i : ℤ) (j : Fin (M.rank i)),
      c i j = (M.model.X i).presheaf.map (homOfLE hVU).op (M.basis i j))
    (p : ℤ) :
    LinearMap.toMatrix (c p) (c (p + 1))
        ((M.model.d p (p + 1)).val.app (Opposite.op V)).hom =
      (M.matrix p).map (X.presheaf.map (homOfLE hVU).op).hom := by
  refine Matrix.ext fun a b => ?_
  have h1 : LinearMap.toMatrix (c p) (c (p + 1))
        ((M.model.d p (p + 1)).val.app (Opposite.op V)).hom a b =
      (c (p + 1)).repr
        (((M.model.d p (p + 1)).val.app (Opposite.op V)).hom (c p b)) a :=
    LinearMap.toMatrix_apply _ _ _ _ _
  have h2 : M.matrix p a b =
      (M.basis (p + 1)).repr
        (((M.model.d p (p + 1)).val.app (Opposite.op U)).hom (M.basis p b)) a :=
    LinearMap.toMatrix_apply _ _ _ _ _
  have h3 : ((M.model.d p (p + 1)).val.app (Opposite.op V)).hom (c p b) =
      (M.model.X (p + 1)).presheaf.map (homOfLE hVU).op
        (((M.model.d p (p + 1)).val.app (Opposite.op U)).hom (M.basis p b)) := by
    rw [hc' p b]
    exact (Scheme.Modules.map_app (M.model.d p (p + 1)) hVU (M.basis p b)).symm
  have h4 : (M.matrix p).map (X.presheaf.map (homOfLE hVU).op).hom a b =
      (X.presheaf.map (homOfLE hVU).op).hom (M.matrix p a b) := rfl
  rw [h1, h3]
  exact ((hc (p + 1) _ a).trans
    (congrArg (fun t => (X.presheaf.map (homOfLE hVU).op).hom t) h2.symm)).trans h4.symm

/-- **The restriction of a bounded-above finite free model to a smaller open, and its effect on
the Fitting ideals.** A finite free model of `K` over `U` restricts to one over any `V ≤ U`, with
the same ranks and the same bound, whose `(p, k)`-th ideal of minors is the base change along
`Γ(X, U) → Γ(X, V)` of the one over `U`.

This is the missing input to a lower bound on the Fitting ideal sheaf of [Stacks, Tag 0ESP]: the
sheaf is `Scheme.IdealSheafData.ofIdeals` of the family of these ideals, and `ofIdeals` recovers a
family only when the family is compatible with passing to a standard open. -/
theorem exists_restrict (M : DerivedFreeModel K U) {V : X.Opens} (hVU : V ≤ U) :
    ∃ M' : DerivedFreeModel K V, M'.rank = M.rank ∧ M'.top = M.top ∧
      ∀ p k : ℤ, M'.fittingIdeal p k =
        Ideal.map (X.presheaf.map (homOfLE hVU).op).hom (M.fittingIdeal p k) := by
  classical
  choose g g' hgg using fun i => M.exists_basis_pair hVU i
  set φ : Γ(X, U) →+* Γ(X, V) := (X.presheaf.map (homOfLE hVU).op).hom with hφ
  set c : ∀ i : ℤ, Module.Basis (Fin (M.rank i)) Γ(X, V) Γ(M.model.X i, V) := fun i =>
    Stacks.basisOfSemilinearImage φ (g i) (g' i) (M.basis i)
    with hcdef
  have hc' : ∀ (i : ℤ) (j : Fin (M.rank i)),
      c i j = (M.model.X i).presheaf.map (homOfLE hVU).op (M.basis i j) := fun i j =>
    Stacks.basisOfSemilinearImage_apply _ _ (Scheme.Modules.resAddHom_smul (M.model.X i) hVU) _ _
      (hgg i) _ j
  have hc : ∀ (i : ℤ) (x : Γ(M.model.X i, U)) (j : Fin (M.rank i)),
      (c i).repr ((M.model.X i).presheaf.map (homOfLE hVU).op x) j =
        φ ((M.basis i).repr x j) := fun i x j =>
    Stacks.basisOfSemilinearImage_repr _ _ (Scheme.Modules.resAddHom_smul (M.model.X i) hVU) _ _
      (hgg i) _ x j
  let M' : DerivedFreeModel K V :=
    { model := M.model
      rank := M.rank
      top := M.top
      rank_eq_zero_of_top_lt := M.rank_eq_zero_of_top_lt
      isFree := fun i => M.isFree_of_le hVU i
      basis := c
      derivedIso := M.derivedIso_of_le hVU }
  refine ⟨M', rfl, rfl, fun p k => ?_⟩
  change minorIdeal (LinearMap.toMatrix (c p) (c (p + 1))
      ((M.model.d p (p + 1)).val.app (Opposite.op V)).hom)
      (M.toFreeData.minorSize p k).toNat =
    Ideal.map φ (M.fittingIdeal p k)
  rw [M.toMatrix_eq_matrix_map hVU c hc hc' p, M.fittingIdeal_eq p k, map_minorIdeal]

end DerivedFreeModel

end AlgebraicGeometry

end
