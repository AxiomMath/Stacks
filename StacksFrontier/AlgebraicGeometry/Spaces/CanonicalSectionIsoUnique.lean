module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RestrictScalarsEssentialImage
public import StacksFrontier.AlgebraicGeometry.Spaces.CanonicalSectionRegular
public import StacksFrontier.AlgebraicGeometry.Spaces.InvertibleQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.ZeroSchemeProperties

/-!
# The isomorphism carrying the canonical section to a given section is unique

Let `X` be an algebraic space over a scheme `S`, let `D ⊆ X` be an effective Cartier divisor and
let `L` be an `𝒪_X`-module with a global section `s`.  Stacks 0847, part (2) asserts that the
effective Cartier divisor `D` and the isomorphism `𝒪_X(D) ≅ L` carrying the canonical section
`1_D` to `s` are *unique*.  This file proves the uniqueness of the isomorphism.

## Main results

* `AlgebraicGeometry.Space.eq_id_of_comp_eq_of_isInvertible`: an endomorphism of an invertible
  `𝒪_X`-module which fixes a regular global section is the identity.
* `AlgebraicGeometry.Space.iso_eq_of_canonicalSectionHom_comp_eq` is the uniqueness clause of
  **Stacks 0847, part (2)**: two isomorphisms `𝒪_X(D) ≅ L` which both send the canonical
  section `1_D` of `𝒪_X(D)` to `s` are equal.

## Implementation notes

The two isomorphisms differ by an endomorphism `u` of `𝒪_X(D)` fixing `1_D`, and the whole
content is that such a `u` is the identity.  On an invertible module every endomorphism is
multiplication by a regular function, and multiplication by `1_D` is injective on sections
because `1_D` is regular — part (1) of the same tag,
`AlgebraicGeometry.Space.canonicalSection_isRegular` — so the function is `1`.  That argument is
carried out chartwise rather than through an identification of the endomorphism ring: by
`Stacks.SheafOfModules.locallyOnCovering_nonempty_over_iso_unit`, which needs only that the
small étale site of an algebraic space is locally ringed, every object of the site has a
covering sieve on each member `V` of which `𝒪_X(D)` is isomorphic to the structure sheaf; an
`𝒪_X(V)`-linear endomorphism of a free module of rank one is multiplication by its coefficient,
and regularity of `1_D` on `V` forces that coefficient to be `1`.  The passage from the members
of the covering sieve back to the object itself is separatedness of a sheaf of modules,
`Stacks.SheafOfModules.ChangeOfRings.sections_ext`.

No trivialization of `𝓘_D` and no local description of `D` enters, and in particular Stacks 083C
— whose equivalences this library does not have — is not used.

## Where the rest of Stacks 0847, part (2) lives

Part (2) asserts that the effective Cartier divisor is unique, that it is the zero scheme `Z(s)`
of Stacks 0845, and that the isomorphism can be chosen to send `1_D` to `s` and is then unique.
This file supplies the last of those.  The other three are
`AlgebraicGeometry.Space.eq_zeroScheme_of_canonicalSectionHom_comp` — an effective Cartier
divisor carrying an isomorphism `𝒪_X(D) ≅ L` which sends `1_D` to `s` is `Z(s)`, so there is at
most one — and the existence half
`AlgebraicGeometry.Space.exists_unique_isEffectiveCartierDivisor_iso_canonicalSectionHom_comp`,
which assembles all four clauses into the statement of the source.

## References

* [Stacks Project, Tag 0847](https://stacks.math.columbia.edu/tag/0847)
* [Stacks Project, Tag 0841](https://stacks.math.columbia.edu/tag/0841)
* [Stacks Project, Tag 0843](https://stacks.math.columbia.edu/tag/0843)
* [Stacks Project, Tag 0B8Q](https://stacks.math.columbia.edu/tag/0B8Q)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-! ### An endomorphism fixing a regular section -/

/-- **An endomorphism of a module free of rank one on a chart, fixing a section which is regular
there, is the identity on that chart.**  The endomorphism is multiplication by the coefficient
`c` by which it moves a basis, fixing the section says that `c` times the coordinate of the
section is that coordinate, and regularity of the section says that multiplication by its
coordinate is injective; so `c = 1`. -/
private theorem app_eq_self_of_linearEquiv
    (M : SheafOfModules.{u} (structureRingSheaf B S hS X)) (σ : M.sections) (u : M ⟶ M)
    (V : SmallEtale B S hS X.1)
    (e : M.val.obj (op V) ≃ₗ[(structureRingSheaf B S hS X).obj.obj (op V)]
      (structureRingSheaf B S hS X).obj.obj (op V))
    (hinj : Function.Injective
      fun r : ToType ((structureRingSheaf B S hS X).obj.obj (op V)) => r • σ.eval (op V))
    (hu : u.val.app (op V) (σ.eval (op V)) = σ.eval (op V))
    (x : M.val.obj (op V)) :
    u.val.app (op V) x = x := by
  have hcomm : ∀ a b : ToType ((structureRingSheaf B S hS X).obj.obj (op V)), a * b = b * a :=
    fun a b => mul_comm (G := ToType ((smallEtaleRingedSite B S hS X.1 X.2).O.obj.obj (op V))) a b
  set c : ToType ((structureRingSheaf B S hS X).obj.obj (op V)) :=
    e (u.val.app (op V) (e.symm 1)) with hc
  have key : ∀ r : ToType ((structureRingSheaf B S hS X).obj.obj (op V)),
      e (u.val.app (op V) (e.symm r)) = r * c := by
    intro r
    have hr : e.symm r = r • e.symm 1 := by
      rw [← map_smul, smul_eq_mul, mul_one]
    rw [hr, map_smul, map_smul, smul_eq_mul, hc]
  have hone : c = 1 := by
    refine hinj ?_
    refine e.injective ?_
    rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul, one_mul, hcomm c (e (σ.eval (op V)))]
    have h := key (e (σ.eval (op V)))
    rw [e.symm_apply_apply, hu] at h
    exact h.symm
  have h := key (e x)
  rw [e.symm_apply_apply, hone, mul_one] at h
  exact e.injective h

/-- **An endomorphism of an invertible `𝒪_X`-module which fixes a regular global section is the
identity.**  By Stacks 0B8Q on the small étale site of an algebraic space the module is trivial
on a covering sieve of every object, and on each member of that sieve the endomorphism is
multiplication by a regular function which regularity of the section pins down to `1`;
separatedness of the module as a sheaf then gives the identity on the object itself. -/
theorem eq_id_of_comp_eq_of_isInvertible
    (M : SheafOfModules.{u} (structureRingSheaf B S hS X))
    (hM : AlgebraicGeometry.SheafOfModules.IsInvertible (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property M)
    (σ : M.sections)
    (hσ : AlgebraicGeometry.IsRegularSection (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property σ)
    (u : M ⟶ M) (hu : M.unitHomEquiv.symm σ ≫ u = M.unitHomEquiv.symm σ) :
    u = 𝟙 M := by
  have hweak : HasWeakSheafify (smallEtaleRingedSite B S hS X.1 X.2).J AddCommGrpCat.{u} :=
    inferInstanceAs (HasWeakSheafify (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u})
  have hloc : (smallEtaleRingedSite B S hS X.1 X.2).J.WEqualsLocallyBijective AddCommGrpCat.{u} :=
    inferInstanceAs ((SmallEtale.topology B S hS X.1).WEqualsLocallyBijective AddCommGrpCat.{u})
  have hinv : Stacks.SheafOfModules.IsInvertible
      (smallEtaleRingedSite B S hS X.1 X.2).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).property M :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hM
  have hsec : SheafOfModules.sectionsMap u σ = σ :=
    M.unitHomEquiv.symm.injective
      ((SheafOfModules.unitHomEquiv_symm_comp σ u).symm.trans hu)
  have hval : ∀ W : (SmallEtale B S hS X.1)ᵒᵖ, u.val.app W (σ.eval W) = σ.eval W :=
    fun W => congrArg (fun t : M.sections => t.eval W) hsec
  have hreg := (isRegularSection_iff_forall_injective_smul B S hS X M σ).1 hσ
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun W => ?_)
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  change u.val.app W x = x
  obtain ⟨T, hT, htriv⟩ := Stacks.SheafOfModules.locallyOnCovering_nonempty_over_iso_unit
    (smallEtaleRingedSite B S hS X.1 X.2).O (structureRingSheaf B S hS X).property M
    (smallEtaleRingedSite_isLocallyRinged B S hS X.1 X.2).2 W.unop
  refine Stacks.SheafOfModules.ChangeOfRings.sections_ext M hT (fun {Y} {g} hg => ?_)
  obtain ⟨eY⟩ := htriv g hg
  have hchart : ∀ y : M.val.obj (op Y), u.val.app (op Y) y = y :=
    app_eq_self_of_linearEquiv B S hS X M σ u Y
      ((SheafOfModules.evaluation ((structureRingSheaf B S hS X).over Y)
        (op (Over.mk (𝟙 Y)))).mapIso eY).toLinearEquiv (hreg (op Y)) (hval (op Y))
  change M.val.map g.op (u.val.app W x) = M.val.map g.op x
  rw [← PresheafOfModules.naturality_apply u.val g.op x]
  exact hchart (M.val.map g.op x)

/-! ### Uniqueness of the isomorphism of Stacks 0847, part (2) -/

variable (D : ClosedSubspaces B S hS X.1) (hD : IsEffectiveCartierDivisor B S hS X D)

/-- **Stacks 0847, part (2): the isomorphism is unique.**  Let `D ⊆ X` be an effective Cartier
divisor on an algebraic space `X` and let `s` be a global section of an `𝒪_X`-module `L`.  Two
isomorphisms `𝒪_X(D) ≅ L` which both carry the canonical section `1_D` of `𝒪_X(D)` to `s` are
equal.

Composing one with the inverse of the other gives an endomorphism of `𝒪_X(D)` fixing `1_D`, and
`AlgebraicGeometry.Space.eq_id_of_comp_eq_of_isInvertible` makes it the identity: `𝒪_X(D)` is
invertible and `1_D` is regular by part (1) of the same tag. -/
@[stacks 0847 "part (2): uniqueness of the isomorphism — two isomorphisms from the sheaf of an \
effective Cartier divisor to an invertible module, both carrying the canonical section to the \
given section, are equal; with no assumed inputs"]
theorem iso_eq_of_canonicalSectionHom_comp_eq
    (L : SheafOfModules.{u} (structureRingSheaf B S hS X)) (s : L.sections)
    (i j : associatedInvertibleSheaf B S hS X D hD ≅ L)
    (hi : canonicalSectionHom B S hS X D hD ≫ i.hom = L.unitHomEquiv.symm s)
    (hj : canonicalSectionHom B S hS X D hD ≫ j.hom = L.unitHomEquiv.symm s) :
    i = j := by
  have hu : canonicalSectionHom B S hS X D hD ≫ (i.hom ≫ j.inv) =
      canonicalSectionHom B S hS X D hD := by
    rw [← Category.assoc, hi, ← hj, Category.assoc, j.hom_inv_id, Category.comp_id]
  have hid : i.hom ≫ j.inv = 𝟙 (associatedInvertibleSheaf B S hS X D hD) :=
    eq_id_of_comp_eq_of_isInvertible B S hS X (associatedInvertibleSheaf B S hS X D hD)
      (associatedInvertibleSheaf_isInvertible B S hS X D hD)
      (canonicalSection B S hS X D hD) (canonicalSection_isRegular B S hS X D hD) _ hu
  refine Iso.ext ?_
  rw [← Category.comp_id i.hom, ← j.inv_hom_id, ← Category.assoc, hid, Category.id_comp]

end AlgebraicGeometry.Space

end
