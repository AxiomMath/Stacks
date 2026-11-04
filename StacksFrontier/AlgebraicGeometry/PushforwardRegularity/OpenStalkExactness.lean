module

public import StacksFrontier.AlgebraicGeometry.PushforwardRegularity.OpenBaseChange
public import StacksFrontier.AlgebraicGeometry.PushforwardRegularity.Quotient

/-!
# The quotient sequence of a flat pushforward at a stalk, after restricting the base

Let `f : X ⟶ S` be a quasi-compact and quasi-separated morphism of schemes, let `F` be an
`𝒪_X`-module flat over `S`, let `s : S` and let `a ∈ 𝒪_{S,s}` be a nonzerodivisor. Inside the
proof of [Stacks, Tag 0EY0] one shrinks `S` to an open neighbourhood `U ∋ s` on which `a` is
represented by an actual section `r`, forms the quotient `F' / r F'` of the inverse image `F'` of
`F` on `X ×_S U`, and reads the exactness statement
`(f_* F)_s --a--> (f_* F)_s ⟶ (f'_* (F'/rF'))_t` off the base-change comparison map
`c : (f_* F)_s ⟶ (f'_* F')_t`.

`StacksFrontier/AlgebraicGeometry/PushforwardRegularity/Quotient.lean` proves that exactness
statement on `S` itself, and
`StacksFrontier/AlgebraicGeometry/PushforwardRegularity/OpenBaseChange.lean` proves that `c` is
an isomorphism of abelian groups. What is missing, and what this file supplies, is the
*semilinearity* of `c` over the ring isomorphism `𝒪_{S,s} ≅ 𝒪_{U,t}` and the transport of
flatness over `S` to flatness over `U`; with those two the statement over `U` follows from the
statement over `S` applied to `f' : X ×_S U ⟶ U`.

Both come from one computation. For an open immersion `h : X' ⟶ X` and an `𝒪_X`-module `M`,
Mathlib's `Scheme.Modules.restrictStalkNatIso` identifies the stalk of `M` at `h x'` with the
stalk of its restriction at `x'`, and that identification is semilinear over `h.stalkMap x'`
(`restrictStalkInv_smul`): on germs it is the statement that the action of `Γ(X', U)` on
`Γ(M ∣_h, U) = Γ(M, h ''ᵁ U)` is the action of `Γ(X, h ''ᵁ U)` transported by `h.appIso U`.
Composing with the comparison of restriction and inverse image gives the semilinear
identification `pullbackStalkComparison` of the stalk of `F` with the stalk of `h^* F`, which is
simultaneously `𝒪_S`-*linear* for the composite morphism to `S` — whence flatness transports —
and the first factor of `c`.

## Main definitions

* `stalkMapM`: the map induced on stalks by a morphism of `𝒪_X`-modules, at the spelling at
  which both stalks carry their module structures.
* `restrictStalkInv`: the comparison of the stalk of `M` at `h x'` with the stalk at `x'` of its
  restriction along an open immersion `h`.
* `pullbackStalkComparison`: the same for the inverse image instead of the restriction.

## Main results

* `stalkMapM_smul`: the stalk map of a morphism of `𝒪_X`-modules is linear.
* `restrictStalkInv_smul`, `pullbackStalkComparison_smul`: both comparisons are semilinear over
  the stalk map of the open immersion.
* `Stacks.RingTheory.Flat.flat_of_ringEquiv`: flatness transports along a ring isomorphism.
* `isFlatOver_pullback_openSquare`: flatness over the base is stable under base change along an
  open immersion of the base.
* `openStalkComparison_smul`: the stalk comparison map of Tag 0EY0 is semilinear over
  `U.ι.stalkMap t`.
* `exists_section_stalkMap_germ_eq`: a germ on the base is represented by a global section of an
  open subscheme.
* `openStalkComparison_cokernel_eq_zero_of_smul`: the `←` half of the exactness statement, which
  assumes nothing about `f` -- no quasi-compactness, no quasi-separatedness, no flatness of `F`
  and no regularity of `a`.
* `openStalkComparison_cokernel_eq_zero_iff`: the exactness statement, for the comparison map.
  Of the four assertions this file assembles, this is the only one needing a finiteness
  hypothesis on `f`, and within it only the forward implication does.
* `exists_nbhd_openStalkComparison_exact`: the three of them packaged as one existential.

## Implementation notes

The multiplication endomorphism `m` of the inverse image is taken as a parameter together with
its action on sections, exactly as in `stalkMap_cokernel_eq_zero_iff`, rather than constructed.
This is what keeps the statement usable both for a multiplication map built on `X ×_S U` and for
one transported from the base, and no such endomorphism exists in Mathlib or in either Lean tree
to reuse.

Several statements are deliberately restated at one spelling before being rewritten with
(`germM_smul` for `PresheafOfModules.germ_smul`, `stalkMapM` for a stalk map, the `hmem`
membership proofs taken as parameters): `TopCat.Presheaf.stalk F x` and
`(TopCat.Presheaf.stalkFunctor C x).obj F` are definitionally equal and not syntactically equal,
as are `X.presheaf` and `(sheafToPresheaf _ _).obj X.sheaf`, and a goal mixing two such
spellings is not type-correct at `implicit` transparency, so `rw` and `simp` refuse it.

`flat_of_ringEquiv` is proved by `Module.Flat.trans` for the algebra structure given by the
inverse isomorphism, rather than by transporting the flatness criterion, because the submodule
lattices are literally the same; Mathlib has no ring-isomorphism transport for `Module.Flat`.

The universe is the single scheme universe `u` throughout.

## References

* [Stacks Project, Tag 0EY0](https://stacks.math.columbia.edu/tag/0EY0)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.OpenBaseChange Stacks.AlgebraicGeometry.PushforwardRegularity

universe u

namespace Stacks.RingTheory.Flat

/-- **Flatness transports along a ring isomorphism.** If `e : R ≃+* R'` and a module carries
actions of both rings that agree through `e`, then flatness over `R` implies flatness over
`R'`. -/
lemma flat_of_ringEquiv {R R' N : Type u} [CommRing R] [CommRing R'] [AddCommGroup N]
    [Module R N] [Module R' N] (e : R ≃+* R')
    (hcompat : ∀ (a : R) (n : N), a • n = e a • n) [Module.Flat R N] :
    Module.Flat R' N := by
  let _ : Algebra R' R := (e.symm : R' →+* R).toAlgebra
  have halg : ∀ (b : R') (x : R), b • x = e.symm b * x := fun _ _ => rfl
  have hflatRR' : Module.Flat R' R := by
    refine Module.Flat.of_linearEquiv (R := R') (N := R) (M := R')
      { toFun := e, invFun := e.symm, map_add' := e.map_add
        map_smul' := fun b x => by
          rw [halg b x, map_mul, e.apply_symm_apply]
          rfl
        left_inv := e.symm_apply_apply, right_inv := e.apply_symm_apply }
  let _ : IsScalarTower R' R N := ⟨fun b x n => by
    rw [halg b x, hcompat (e.symm b * x) n, map_mul, e.apply_symm_apply, mul_smul,
      hcompat x n]⟩
  exact Module.Flat.trans R' R N

/-- Left regularity transports along a ring isomorphism. -/
lemma isSMulRegular_ringEquiv {R R' : Type*} [CommRing R] [CommRing R'] (e : R ≃+* R')
    {a : R} (ha : IsSMulRegular R a) : IsSMulRegular R' (e a) := by
  intro x y hxy
  simp only [smul_eq_mul] at hxy
  have h2 : e.symm (e a * x) = e.symm (e a * y) := congrArg e.symm hxy
  rw [map_mul, map_mul, e.symm_apply_apply] at h2
  exact e.symm.injective (ha (by simpa only [smul_eq_mul] using h2))

end Stacks.RingTheory.Flat

namespace Stacks.AlgebraicGeometry.OpenStalkExactness

open Stacks.RingTheory.Flat

variable {X S : Scheme.{u}}

/-! ### Stalk maps of morphisms of modules -/

/-- `PresheafOfModules.germ_smul`, restated with the structure sheaf of the scheme spelled
`X.presheaf`, which is the spelling the statements below can be rewritten with. -/
lemma germM_smul (M : X.Modules) (y : X) (W : X.Opens) (hy : y ∈ W) (r : Γ(X, W))
    (m : Γ(M, W)) :
    TopCat.Presheaf.germ M.val.presheaf W y hy (r • m) =
      X.presheaf.germ W y hy r • TopCat.Presheaf.germ M.val.presheaf W y hy m :=
  PresheafOfModules.germ_smul M.val y W hy r m

/-- The map on stalks induced by a morphism of `𝒪_X`-modules, at the spelling at which the two
stalks carry their module structures. -/
noncomputable def stalkMapM {M N : X.Modules} (φ : M ⟶ N) (y : X) :
    TopCat.Presheaf.stalk (C := Ab.{u}) M.val.presheaf y ⟶
      TopCat.Presheaf.stalk (C := Ab.{u}) N.val.presheaf y :=
  (TopCat.Presheaf.stalkFunctor Ab.{u} y).map φ.mapPresheaf

/-- `stalkMapM` sends a germ to the germ of the image. -/
lemma stalkMapM_germ {M N : X.Modules} (φ : M ⟶ N) (y : X) {W : X.Opens} (hy : y ∈ W)
    (ξ : Γ(M, W)) :
    stalkMapM φ y (TopCat.Presheaf.germ M.val.presheaf W y hy ξ) =
      TopCat.Presheaf.germ N.val.presheaf W y hy (φ.app W ξ) :=
  stalkMap_germ M φ y hy ξ

/-- **The stalk map of a morphism of `𝒪_X`-modules is linear** over the stalk of `𝒪_X`. -/
lemma stalkMapM_smul {M N : X.Modules} (φ : M ⟶ N) (y : X) (ρ : X.presheaf.stalk y)
    (n : TopCat.Presheaf.stalk (C := Ab.{u}) M.val.presheaf y) :
    stalkMapM φ y (ρ • n) = ρ • stalkMapM φ y n := by
  obtain ⟨V, hyV, ξ, hξ⟩ := X.presheaf.exists_germ_eq ρ
  obtain ⟨W, hWV, hyW, ζ, hζ⟩ := TopCat.Presheaf.exists_le_germ_eq M.val.presheaf n hyV
  subst hξ
  subst hζ
  have key : ∀ (r : Γ(X, W)) (m : Γ(M, W)),
      stalkMapM φ y (X.presheaf.germ W y hyW r •
          TopCat.Presheaf.germ M.val.presheaf W y hyW m) =
        X.presheaf.germ W y hyW r •
          stalkMapM φ y (TopCat.Presheaf.germ M.val.presheaf W y hyW m) := by
    intro r m
    rw [← germM_smul M y W hyW r m, stalkMapM_germ φ y hyW,
      stalkMapM_germ φ y hyW m, ← germM_smul N y W hyW r (φ.app W m)]
    congr 1
    exact Scheme.Modules.Hom.app_smul φ r m
  rw [← X.presheaf.germ_res_apply (homOfLE hWV) y hyW ξ]
  exact key _ ζ

/-- An isomorphism of `𝒪_X`-modules induces an isomorphism on stalks. -/
lemma isIso_stalkMapM {M N : X.Modules} (φ : M ⟶ N) [IsIso φ] (y : X) :
    IsIso (stalkMapM φ y) :=
  letI : IsIso φ.mapPresheaf := isIso_mapPresheaf φ
  Functor.map_isIso (TopCat.Presheaf.stalkFunctor Ab.{u} y) φ.mapPresheaf

/-! ### Restriction along an open immersion, on stalks -/

section Restrict

variable {X' : Scheme.{u}} (h : X' ⟶ X) [IsOpenImmersion h] (M : X.Modules) (x' : X')

/-- The comparison of the stalk of a module at `h x'` with the stalk at `x'` of its restriction
along the open immersion `h`, at the spelling at which both stalks carry their module
structures. -/
noncomputable def restrictStalkInv :
    TopCat.Presheaf.stalk (C := Ab.{u}) M.val.presheaf (h.base x') ⟶
      TopCat.Presheaf.stalk (C := Ab.{u})
        ((Scheme.Modules.restrictFunctor h).obj M).val.presheaf x' :=
  (Scheme.Modules.restrictStalkNatIso h x').inv.app M

lemma isIso_restrictStalkInv : IsIso (restrictStalkInv h M x') :=
  inferInstanceAs (IsIso ((Scheme.Modules.restrictStalkNatIso h x').inv.app M))

/-- The action of a section of `𝒪_{X'}` on a section of the restriction of `M` is the action of
its image under `h.appIso` on the corresponding section of `M`. -/
lemma restrict_smul {U : X'.Opens} (r : Γ(X', U)) (m : Γ(M, h ''ᵁ U)) :
    HSMul.hSMul (α := Γ(X', U))
        (β := Γ((Scheme.Modules.restrictFunctor h).obj M, U)) r m =
      (h.appIso U).inv r • m :=
  rfl

/-- `restrictStalkInv` sends the germ of a section over `h ''ᵁ U` to its germ over `U`. -/
lemma restrictStalkInv_germ {U : X'.Opens} (hxU : x' ∈ U)
    (hmem : h.base x' ∈ (h ''ᵁ U : X.Opens)) (ξ : Γ(M, h ''ᵁ U)) :
    restrictStalkInv h M x'
        (TopCat.Presheaf.germ M.val.presheaf (h ''ᵁ U) (h.base x') hmem ξ) =
      TopCat.Presheaf.germ
        ((Scheme.Modules.restrictFunctor h).obj M).val.presheaf U x' hxU ξ :=
  ConcreteCategory.congr_hom
    (Scheme.Modules.germ_restrictStalkNatIso_inv_app h x' M hxU) ξ

/-- The stalk map of an open immersion, on the germ of a section transported by `h.appIso`. -/
lemma stalkMap_germ_appIso {U : X'.Opens} (hxU : x' ∈ U)
    (hmem : h.base x' ∈ (h ''ᵁ U : X.Opens)) (r : Γ(X, h ''ᵁ U)) :
    h.stalkMap x' (X.presheaf.germ (h ''ᵁ U) (h.base x') hmem r) =
      X'.presheaf.germ U x' hxU ((h.appIso U).hom r) := by
  rw [Scheme.Hom.germ_stalkMap_apply h (h ''ᵁ U) x' hmem r, Scheme.Hom.appIso_hom' h U,
    Scheme.Hom.appLE, CommRingCat.comp_apply,
    X'.presheaf.germ_res_apply (homOfLE (Scheme.Hom.preimage_image_eq h U).ge) x' hxU]

/-- **The stalk comparison for a restriction is semilinear** over the stalk map of the open
immersion. -/
lemma restrictStalkInv_smul (rho : X.presheaf.stalk (h.base x'))
    (n : TopCat.Presheaf.stalk (C := Ab.{u}) M.val.presheaf (h.base x')) :
    restrictStalkInv h M x' (rho • n) =
      h.stalkMap x' rho • restrictStalkInv h M x' n := by
  obtain ⟨V, hV, xi, hxi⟩ := X.presheaf.exists_germ_eq rho
  obtain ⟨W, hWV, hW, zeta, hzeta⟩ := TopCat.Presheaf.exists_le_germ_eq M.val.presheaf n hV
  subst hxi
  subst hzeta
  set U : X'.Opens := h ⁻¹ᵁ W with hU
  have hxU : x' ∈ U := hW
  have himg : (h ''ᵁ U : X.Opens) ≤ W := h.image_preimage_le W
  have hmem : h.base x' ∈ (h ''ᵁ U : X.Opens) := ⟨x', hxU, rfl⟩
  have key : ∀ (r : Γ(X, h ''ᵁ U)) (m : Γ(M, h ''ᵁ U)),
      restrictStalkInv h M x'
          (X.presheaf.germ (h ''ᵁ U) (h.base x') hmem r •
            TopCat.Presheaf.germ M.val.presheaf (h ''ᵁ U) (h.base x') hmem m) =
        h.stalkMap x' (X.presheaf.germ (h ''ᵁ U) (h.base x') hmem r) •
          restrictStalkInv h M x'
            (TopCat.Presheaf.germ M.val.presheaf (h ''ᵁ U) (h.base x') hmem m) := by
    intro r m
    rw [← germM_smul M (h.base x') (h ''ᵁ U) hmem r m,
      restrictStalkInv_germ h M x' hxU hmem, restrictStalkInv_germ h M x' hxU hmem,
      stalkMap_germ_appIso h x' hxU hmem r,
      ← germM_smul ((Scheme.Modules.restrictFunctor h).obj M) x' U hxU
        ((h.appIso U).hom r) m]
    congr 1
    rw [restrict_smul h M ((h.appIso U).hom r) m]
    exact congrArg (fun z => z • m) ((h.appIso U).hom_inv_id_apply r).symm
  rw [← X.presheaf.germ_res_apply (homOfLE (himg.trans hWV)) (h.base x') hmem xi,
    ← TopCat.Presheaf.germ_res_apply M.val.presheaf (homOfLE himg) (h.base x') hmem zeta]
  exact key _ _

end Restrict

/-! ### Inverse image along an open immersion, on stalks -/

section PullbackStalk

variable {X' : Scheme.{u}} (g' : X' ⟶ X) [IsOpenImmersion g'] (F : X.Modules) (x' : X')

/-- The comparison of the stalk of `F` at `g' x'` with the stalk at `x'` of its inverse image
along the open immersion `g'`. -/
noncomputable def pullbackStalkComparison :
    TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf (g'.base x') ⟶
      TopCat.Presheaf.stalk (C := Ab.{u})
        ((Scheme.Modules.pullback g').obj F).val.presheaf x' :=
  restrictStalkInv g' F x' ≫
    stalkMapM ((Scheme.Modules.restrictFunctorIsoPullback g').hom.app F) x'

lemma bijective_pullbackStalkComparison :
    Function.Bijective (pullbackStalkComparison g' F x') := by
  have h1 := isIso_restrictStalkInv g' F x'
  have h2 := isIso_stalkMapM
    ((Scheme.Modules.restrictFunctorIsoPullback g').hom.app F) x'
  have : IsIso (pullbackStalkComparison g' F x') :=
    @IsIso.comp_isIso _ _ _ _ _ _ _ h1 h2
  exact ConcreteCategory.bijective_of_isIso _

/-- **The comparison with the stalk of the inverse image is semilinear** over the stalk map of
the open immersion. -/
lemma pullbackStalkComparison_smul (rho : X.presheaf.stalk (g'.base x'))
    (n : TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf (g'.base x')) :
    pullbackStalkComparison g' F x' (rho • n) =
      g'.stalkMap x' rho • pullbackStalkComparison g' F x' n := by
  change stalkMapM _ x' (restrictStalkInv g' F x' (rho • n)) =
    g'.stalkMap x' rho • stalkMapM _ x' (restrictStalkInv g' F x' n)
  rw [restrictStalkInv_smul g' F x' rho n, stalkMapM_smul]

end PullbackStalk

/-! ### Flatness over the base under base change along an open immersion of the base -/

section FlatBaseChange

/-- The stalk map of a composite, evaluated on an element. -/
private lemma stalkMap_comp_apply {Y Z : Scheme.{u}} (g : X ⟶ Y) (f : Y ⟶ Z) (x : X)
    (a : Z.presheaf.stalk (f.base (g.base x))) :
    (g ≫ f).stalkMap x a = g.stalkMap x (f.stalkMap (g.base x) a) :=
  (ConcreteCategory.congr_hom (Scheme.Hom.stalkMap_comp g f x) a).trans
    (CommRingCat.comp_apply _ _ a)

variable (f : X ⟶ S) {X' : Scheme.{u}} (g' : X' ⟶ X) [IsOpenImmersion g'] (F : X.Modules)

/-- Flatness over the base is inherited by the inverse image along an open immersion, for the
composite morphism to the original base. -/
lemma isFlatOverAt_pullback_comp (x' : X')
    (hflat : IsFlatOverAt f.toLRSHom.toShHom F (g'.base x')) :
    IsFlatOverAt (g' ≫ f).toLRSHom.toShHom
      ((Scheme.Modules.pullback g').obj F) x' := by
  let N0 := TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf (g'.base x')
  let N := TopCat.Presheaf.stalk (C := Ab.{u})
    ((Scheme.Modules.pullback g').obj F).val.presheaf x'
  let R := S.presheaf.stalk (f.base (g'.base x'))
  let _ : Module R N0 := Module.compHom _ (f.stalkMap (g'.base x')).hom
  let _ : Module R N := Module.compHom _ ((g' ≫ f).stalkMap x').hom
  have hF : Module.Flat R N0 := hflat
  have hsmul0 : ∀ (a : R) (n : N0), a • n = f.stalkMap (g'.base x') a • n :=
    fun _ _ => rfl
  have hsmul : ∀ (a : R) (m : N), a • m = (g' ≫ f).stalkMap x' a • m := fun _ _ => rfl
  have hlin : ∀ (a : R) (n : N0),
      pullbackStalkComparison g' F x' (a • n) = a • pullbackStalkComparison g' F x' n := by
    intro a n
    rw [hsmul0, pullbackStalkComparison_smul, hsmul, stalkMap_comp_apply]
  let e : N0 ≃ₗ[R] N := LinearEquiv.ofBijective
    { toFun := pullbackStalkComparison g' F x'
      map_add' := fun a b => map_add (pullbackStalkComparison g' F x').hom a b
      map_smul' := hlin }
    (bijective_pullbackStalkComparison g' F x')
  exact Module.Flat.of_linearEquiv (R := R) (M := N0) (N := N) e.symm

/-- **Flatness over the base is stable under base change along an open immersion of the base.**
For a commutative square whose two horizontal arrows are open immersions, the inverse image of a
module flat over `S` is flat over `S'`. -/
lemma isFlatOver_pullback_openSquare {S' : Scheme.{u}} {f' : X' ⟶ S'} {g : S' ⟶ S}
    [IsOpenImmersion g] (w : g' ≫ f = f' ≫ g)
    (hflat : IsFlatOver f.toLRSHom.toShHom F) :
    IsFlatOver f'.toLRSHom.toShHom ((Scheme.Modules.pullback g').obj F) := by
  intro x'
  have h1 : IsFlatOverAt (g' ≫ f).toLRSHom.toShHom
      ((Scheme.Modules.pullback g').obj F) x' :=
    isFlatOverAt_pullback_comp f g' F x' (hflat _)
  rw [w] at h1
  let N := TopCat.Presheaf.stalk (C := Ab.{u})
    ((Scheme.Modules.pullback g').obj F).val.presheaf x'
  let R := S.presheaf.stalk (g.base (f'.base x'))
  let R' := S'.presheaf.stalk (f'.base x')
  let _ : Module R N := Module.compHom _ ((f' ≫ g).stalkMap x').hom
  let _ : Module R' N := Module.compHom _ (f'.stalkMap x').hom
  have hF : Module.Flat R N := h1
  have hiso : IsIso (g.stalkMap (f'.base x')) := inferInstance
  let e : R ≃+* R' :=
    (asIso (g.stalkMap (f'.base x'))).commRingCatIsoToRingEquiv
  have he : ∀ a : R, e a = g.stalkMap (f'.base x') a := fun _ => rfl
  have hcompat : ∀ (a : R) (n : N), a • n = e a • n := by
    intro a n
    change (f' ≫ g).stalkMap x' a • n = f'.stalkMap x' (e a) • n
    rw [he, stalkMap_comp_apply]
  exact flat_of_ringEquiv (R := R) (R' := R') (N := N) e hcompat

end FlatBaseChange

/-! ### The stalk comparison map of Tag 0EY0 -/

section Exactness

variable (f : X ⟶ S) (F : X.Modules)

/-- The three factors of `openStalkComparison`, as nested applications. -/
lemma openStalkComparison_apply (U : S.Opens) (t : U.toScheme)
    (x : TopCat.Presheaf.stalk (C := Ab.{u})
      ((Scheme.Modules.pushforward f).obj F).val.presheaf (U.ι.base t)) :
    openStalkComparison f U F t x =
      stalkMapM ((AffinePushforward.baseChangeNatTrans
          (IsPullback.of_hasPullback f U.ι).w).app F) t
        (stalkMapM ((Scheme.Modules.restrictFunctorIsoPullback U.ι).hom.app
            ((Scheme.Modules.pushforward f).obj F)) t
          (restrictStalkInv U.ι ((Scheme.Modules.pushforward f).obj F) t x)) :=
  rfl

/-- **The stalk comparison map of [Stacks, Tag 0EY0] is semilinear** over the stalk map of the
open immersion `U.ι`. Its first factor is the restriction comparison, which is semilinear, and
its other two factors are stalk maps of morphisms of `𝒪_U`-modules, which are linear. -/
lemma openStalkComparison_smul (U : S.Opens) (t : U.toScheme)
    (z : S.presheaf.stalk (U.ι.base t))
    (x : TopCat.Presheaf.stalk (C := Ab.{u})
      ((Scheme.Modules.pushforward f).obj F).val.presheaf (U.ι.base t)) :
    openStalkComparison f U F t (z • x) =
      U.ι.stalkMap t z • openStalkComparison f U F t x := by
  rw [openStalkComparison_apply, openStalkComparison_apply,
    restrictStalkInv_smul, stalkMapM_smul, stalkMapM_smul]

/-- The stalk map of `U.ι` sends the germ of a section of `𝒪_S` over `U` to the germ of the
corresponding global section of the open subscheme `U`. -/
lemma stalkMap_germ_toScheme (U : S.Opens) (t : U.toScheme) (ht : U.ι.base t ∈ U)
    (r₀ : Γ(S, U)) :
    ∃ r : Γ(U.toScheme, (⊤ : U.toScheme.Opens)),
      U.ι.stalkMap t (S.presheaf.germ U (U.ι.base t) ht r₀) =
        U.toScheme.presheaf.germ ⊤ t trivial r := by
  have hle : (⊤ : U.toScheme.Opens) ≤ U.ι ⁻¹ᵁ U := fun x _ => x.2
  refine ⟨U.toScheme.presheaf.map (homOfLE hle).op (U.ι.app U r₀), ?_⟩
  rw [U.toScheme.presheaf.germ_res_apply (homOfLE hle) t trivial,
    Scheme.Hom.germ_stalkMap_apply U.ι U t ht r₀]

/-- A germ on the base is represented by a global section of an open subscheme. -/
lemma exists_section_stalkMap_germ_eq (s : S) (a : S.presheaf.stalk s) :
    ∃ (U : S.Opens) (hs : s ∈ U) (r : Γ(U.toScheme, (⊤ : U.toScheme.Opens))),
      U.ι.stalkMap ⟨s, hs⟩ a = U.toScheme.presheaf.germ ⊤ ⟨s, hs⟩ trivial r := by
  obtain ⟨U, hs, r₀, hr₀⟩ := S.presheaf.exists_germ_eq a
  obtain ⟨r, hr⟩ := stalkMap_germ_toScheme U ⟨s, hs⟩ hs r₀
  exact ⟨U, hs, r, by rw [← hr₀]; exact hr⟩

/-- **Divisibility implies vanishing, with nothing assumed about `f`.** This is the `←` half of
`openStalkComparison_cokernel_eq_zero_iff`, isolated because it needs none of that statement's
hypotheses beyond the multiplication rule for `m`: not quasi-compactness, not
quasi-separatedness, not flatness of `F`, and not regularity of `a`. It is the forward
implication alone that is geometric. -/
theorem openStalkComparison_cokernel_eq_zero_of_smul (U : S.Opens) (t : U.toScheme)
    (r : Γ(U.toScheme, (⊤ : U.toScheme.Opens)))
    (a : S.presheaf.stalk (U.ι.base t))
    (hab : U.ι.stalkMap t a = U.toScheme.presheaf.germ ⊤ t trivial r)
    (m : (Scheme.Modules.pullback (pullback.fst f U.ι)).obj F ⟶
      (Scheme.Modules.pullback (pullback.fst f U.ι)).obj F)
    (hm : ∀ (W : (pullback f U.ι).Opens)
      (hW : W ≤ pullback.snd f U.ι ⁻¹ᵁ (⊤ : U.toScheme.Opens))
      (z : Γ((Scheme.Modules.pullback (pullback.fst f U.ι)).obj F, W)),
      m.app W z = ((pullback.snd f U.ι).appLE ⊤ W hW r) • z)
    (x : TopCat.Presheaf.stalk (C := Ab.{u})
      ((Scheme.Modules.pushforward f).obj F).val.presheaf (U.ι.base t))
    (hx : ∃ y, x = a • y) :
    (TopCat.Presheaf.stalkFunctor Ab.{u} t).map
        ((Scheme.Modules.pushforward (pullback.snd f U.ι)).map
          (cokernel.π m)).mapPresheaf
        (openStalkComparison f U F t x) = 0 := by
  obtain ⟨y, rfl⟩ := hx
  rw [openStalkComparison_smul, hab]
  exact stalkMap_cokernel_eq_zero_of_smul (pullback.snd f U.ι) _ m r hm t trivial _

/-- **Exactness of the pushforward quotient sequence at a stalk, read off the base-change
comparison map.** Let `f` be quasi-compact and quasi-separated, let `F` be flat over `S`, let
`r` be a global section of `𝒪_U` for an open `U` of `S` whose germ at `t` corresponds to the
nonzerodivisor `a ∈ 𝒪_{S,s}`, and let `m` be multiplication by the pullback of `r` on the
inverse image of `F` on `X ×_S U`. An element of `(f_* F)_s` is sent to zero by the stalk map of
`f'_*(F' ⟶ F'/rF')` composed with the comparison map exactly when it is divisible by `a`. -/
theorem openStalkComparison_cokernel_eq_zero_iff [QuasiCompact f] [QuasiSeparated f]
    (hflat : IsFlatOver f.toLRSHom.toShHom F) (U : S.Opens) (t : U.toScheme)
    (r : Γ(U.toScheme, (⊤ : U.toScheme.Opens)))
    (a : S.presheaf.stalk (U.ι.base t))
    (hab : U.ι.stalkMap t a = U.toScheme.presheaf.germ ⊤ t trivial r)
    (ha : IsSMulRegular (S.presheaf.stalk (U.ι.base t)) a)
    (m : (Scheme.Modules.pullback (pullback.fst f U.ι)).obj F ⟶
      (Scheme.Modules.pullback (pullback.fst f U.ι)).obj F)
    (hm : ∀ (W : (pullback f U.ι).Opens)
      (hW : W ≤ pullback.snd f U.ι ⁻¹ᵁ (⊤ : U.toScheme.Opens))
      (z : Γ((Scheme.Modules.pullback (pullback.fst f U.ι)).obj F, W)),
      m.app W z = ((pullback.snd f U.ι).appLE ⊤ W hW r) • z)
    (x : TopCat.Presheaf.stalk (C := Ab.{u})
      ((Scheme.Modules.pushforward f).obj F).val.presheaf (U.ι.base t)) :
    (TopCat.Presheaf.stalkFunctor Ab.{u} t).map
        ((Scheme.Modules.pushforward (pullback.snd f U.ι)).map
          (cokernel.π m)).mapPresheaf
        (openStalkComparison f U F t x) = 0 ↔
      ∃ y, x = a • y := by
  have hflatU : IsFlatOver (pullback.snd f U.ι).toLRSHom.toShHom
      ((Scheme.Modules.pullback (pullback.fst f U.ι)).obj F) :=
    isFlatOver_pullback_openSquare f (pullback.fst f U.ι) F
      (IsPullback.of_hasPullback f U.ι).w hflat
  have hb : IsSMulRegular (U.toScheme.presheaf.stalk t)
      (U.toScheme.presheaf.germ ⊤ t trivial r) := by
    rw [← hab]
    exact isSMulRegular_ringEquiv
      (asIso (U.ι.stalkMap t)).commRingCatIsoToRingEquiv ha
  have hinj := (ConcreteCategory.bijective_of_isIso (openStalkComparison f U F t)).1
  have hinvhom : ∀ w, openStalkComparison f U F t
      ((asIso (openStalkComparison f U F t)).inv w) = w := fun w =>
    (asIso (openStalkComparison f U F t)).inv_hom_id_apply w
  refine ⟨fun hx => ?_,
    openStalkComparison_cokernel_eq_zero_of_smul f F U t r a hab m hm x⟩
  obtain ⟨z, hz⟩ := (stalkMap_cokernel_eq_zero_iff (pullback.snd f U.ι) _ hflatU m r hm t
    trivial hb _).mp hx
  refine ⟨(asIso (openStalkComparison f U F t)).inv z, hinj ?_⟩
  rw [openStalkComparison_smul, hab, hinvhom z]
  exact hz

/-- **The step inside the proof of [Stacks, Tag 0EY0] that shrinks the base.** For `f`
quasi-compact and quasi-separated and `F` flat over `S`, every nonzerodivisor `a ∈ 𝒪_{S,s}` is
the germ of a global section `r` of the structure sheaf of an open neighbourhood `U ∋ s`; the
stalk comparison map `c : (f_* F)_s ⟶ (f'_* F')_t` for the square cutting out `X ×_S U` is
semilinear over `U.ι.stalkMap t`; and an element of `(f_* F)_s` dies in `(f'_* (F'/rF'))_t`
exactly when it is divisible by `a`.

This is the clause of Tag 0EY0 that is stated over a shrunken base; part (4) over `S` itself is
`isSMulRegular_stalk_pushforward`. -/
@[stacks 0EY0 "stalk exactness after shrinking the base"]
theorem exists_nbhd_openStalkComparison_exact [QuasiCompact f] [QuasiSeparated f]
    (hflat : IsFlatOver f.toLRSHom.toShHom F) (s : S) (a : S.presheaf.stalk s)
    (ha : IsSMulRegular (S.presheaf.stalk s) a) :
    ∃ (U : S.Opens) (hs : s ∈ U) (r : Γ(U.toScheme, (⊤ : U.toScheme.Opens))),
      let t : U.toScheme := ⟨s, hs⟩
      U.ι.stalkMap t a = U.toScheme.presheaf.germ ⊤ t trivial r ∧
      (∀ (z : S.presheaf.stalk s)
          (x : TopCat.Presheaf.stalk (C := Ab.{u})
            ((Scheme.Modules.pushforward f).obj F).val.presheaf s),
        openStalkComparison f U F t (z • x) =
          U.ι.stalkMap t z • openStalkComparison f U F t x) ∧
      ∀ (m : (Scheme.Modules.pullback (pullback.fst f U.ι)).obj F ⟶
          (Scheme.Modules.pullback (pullback.fst f U.ι)).obj F),
        (∀ (W : (pullback f U.ι).Opens)
          (hW : W ≤ pullback.snd f U.ι ⁻¹ᵁ (⊤ : U.toScheme.Opens))
          (z : Γ((Scheme.Modules.pullback (pullback.fst f U.ι)).obj F, W)),
          m.app W z = ((pullback.snd f U.ι).appLE ⊤ W hW r) • z) →
        ∀ x : TopCat.Presheaf.stalk (C := Ab.{u})
            ((Scheme.Modules.pushforward f).obj F).val.presheaf s,
          (TopCat.Presheaf.stalkFunctor Ab.{u} t).map
              ((Scheme.Modules.pushforward (pullback.snd f U.ι)).map
                (cokernel.π m)).mapPresheaf
              (openStalkComparison f U F t x) = 0 ↔
            ∃ y, x = a • y := by
  obtain ⟨U, hs, r, hab⟩ := exists_section_stalkMap_germ_eq s a
  exact ⟨U, hs, r, hab, fun z x => openStalkComparison_smul f F U ⟨s, hs⟩ z x,
    fun m hm x =>
      openStalkComparison_cokernel_eq_zero_iff f F hflat U ⟨s, hs⟩ r a hab ha m hm x⟩

end Exactness

end Stacks.AlgebraicGeometry.OpenStalkExactness

end
