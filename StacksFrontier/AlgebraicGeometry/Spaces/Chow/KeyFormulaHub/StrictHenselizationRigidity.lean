module

public import StacksFrontier.RingTheory.Etale.IndEtaleUniverse
public import StacksFrontier.RingTheory.Henselian.Henselization.Defs
public import StacksFrontier.RingTheory.Henselian.StrictHenselization

/-!
# A local map between strict henselizations is an isomorphism

Let `A` be a ring and let `R₁`, `R₂` be henselian local `A`-algebras which are ind-étale over `A`.
A local `A`-algebra map `f : R₁ → R₂` which is bijective on residue fields is bijective: the map
of the universal property of the strict henselization (Stacks 04GU) in the other direction,
along the inverse of the residue field isomorphism, is a two-sided inverse, by the uniqueness half
of that universal property.

The residue field condition holds as soon as the residue field of `R₁` is separably closed and the
residue field of `R₂` is separable over a common subfield, which is the situation of two strict
henselizations of one local ring.

## Main results

* `StacksDraft.bijective_of_indEtale_of_bijective_residueField_map`: the rigidity statement.
* `StacksDraft.bijective_residueField_map_of_isSeparable`: the residue field condition from
  separable closedness of the source and separability of the target.

## References

* [Stacks Project, Tag 04GU](https://stacks.math.columbia.edu/tag/04GU)
* [Stacks Project, Tag 08HT](https://stacks.math.columbia.edu/tag/08HT)
-/

@[expose] public section

open IsLocalRing

universe u v w

namespace StacksDraft

/-- An endomorphism of a henselian local ind-étale `A`-algebra which is local and induces the
identity on residue fields is the identity. -/
private theorem algHom_eq_id_of_residue {A : Type u} {R : Type v} [CommRing A] [CommRing R]
    [HenselianLocalRing R] [Algebra A R] (h : IndEtale A R) (g : R →ₐ[A] R)
    (hg : IsLocalHom g) (hres : ∀ x, residue R (g x) = residue R x) : g = AlgHom.id A R :=
  have hid : (RingHom.id (ResidueField R)).comp ((residue R).comp (algebraMap A R)) =
      (residue R).comp (algebraMap A R) := rfl
  (HenselianLocalRing.indEtaleAlgHomOfResidue_unique h _ hid _ hg (RingHom.ext hres)).trans
    (HenselianLocalRing.indEtaleAlgHomOfResidue_unique h _ hid _ ⟨fun _ ha ↦ ha⟩ rfl).symm

/-- **Rigidity of strict henselizations.** A local `A`-algebra map between henselian local
ind-étale `A`-algebras which is bijective on residue fields is bijective. -/
theorem bijective_of_indEtale_of_bijective_residueField_map {A : Type u} {R₁ : Type v}
    {R₂ : Type w} [CommRing A] [CommRing R₁] [CommRing R₂] [IsLocalRing R₁] [IsLocalRing R₂]
    [HenselianLocalRing R₁] [HenselianLocalRing R₂] [Algebra A R₁] [Algebra A R₂]
    (h₁ : IndEtale A R₁) (h₂ : IndEtale A R₂) (f : R₁ →ₐ[A] R₂) (hfloc : IsLocalHom f)
    (hf : Function.Bijective
      (letI : IsLocalHom (f : R₁ →+* R₂) := ⟨fun a ha ↦ hfloc.map_nonunit a ha⟩
       ResidueField.map (f : R₁ →+* R₂))) :
    Function.Bijective f := by
  let : IsLocalHom (f : R₁ →+* R₂) := ⟨fun a ha ↦ hfloc.map_nonunit a ha⟩
  set e := RingEquiv.ofBijective _ hf with he
  have hcomm (x : R₁) : residue R₂ (f x) = e (residue R₁ x) :=
    (ResidueField.map_residue (f : R₁ →+* R₂) x).symm
  have hφ : (e.symm : ResidueField R₂ →+* ResidueField R₁).comp
      ((residue R₂).comp (algebraMap A R₂)) = (residue R₁).comp (algebraMap A R₁) := by
    refine RingHom.ext fun a ↦ ?_
    show e.symm (residue R₂ (algebraMap A R₂ a)) = residue R₁ (algebraMap A R₁ a)
    rw [← f.commutes a, hcomm, RingEquiv.symm_apply_apply]
  set g := HenselianLocalRing.indEtaleAlgHomOfResidue h₂
    (e.symm : ResidueField R₂ →+* ResidueField R₁) hφ with hgdef
  have hgres (y : R₂) : residue R₁ (g y) = e.symm (residue R₂ y) :=
    RingHom.congr_fun (HenselianLocalRing.comp_residue_indEtaleAlgHomOfResidue h₂
      (e.symm : ResidueField R₂ →+* ResidueField R₁) hφ) y
  have hgloc : IsLocalHom g :=
    HenselianLocalRing.isLocalHom_indEtaleAlgHomOfResidue h₂ _ hφ
  have hgf : g.comp f = AlgHom.id A R₁ :=
    algHom_eq_id_of_residue h₁ _
      ⟨fun a ha ↦ hfloc.map_nonunit a (hgloc.map_nonunit (f a) ha)⟩ fun x ↦ by
        rw [AlgHom.comp_apply, hgres, hcomm, RingEquiv.symm_apply_apply]
  have hfg : f.comp g = AlgHom.id A R₂ :=
    algHom_eq_id_of_residue h₂ _
      ⟨fun a ha ↦ hgloc.map_nonunit a (hfloc.map_nonunit (g a) ha)⟩ fun y ↦ by
        rw [AlgHom.comp_apply, hcomm, hgres, RingEquiv.apply_symm_apply]
  exact Function.bijective_iff_has_inverse.2
    ⟨g, fun x ↦ AlgHom.congr_fun hgf x, fun y ↦ AlgHom.congr_fun hfg y⟩

/-- **The residue field condition for two strict henselizations.** A local map `f : R₁ → R₂` of
local rings whose residue fields are extensions of a common field `K`, compatibly with `f`, is
bijective on residue fields as soon as the residue field of `R₁` is separably closed and the
residue field of `R₂` is separable over `K`. -/
theorem bijective_residueField_map_of_isSeparable {R₁ : Type v} {R₂ : Type w} [CommRing R₁]
    [CommRing R₂] [IsLocalRing R₁] [IsLocalRing R₂] (f : R₁ →+* R₂) [IsLocalHom f]
    {K : Type u} [Field K] [Algebra K (ResidueField R₁)] [Algebra K (ResidueField R₂)]
    (hK : (ResidueField.map f).comp (algebraMap K (ResidueField R₁)) =
      algebraMap K (ResidueField R₂))
    [IsSepClosed (ResidueField R₁)] [Algebra.IsSeparable K (ResidueField R₂)] :
    Function.Bijective (ResidueField.map f) := by
  let : Algebra (ResidueField R₁) (ResidueField R₂) := (ResidueField.map f).toAlgebra
  have : IsScalarTower K (ResidueField R₁) (ResidueField R₂) :=
    IsScalarTower.of_algebraMap_eq fun k ↦ (RingHom.congr_fun hK k).symm
  have : Algebra.IsSeparable (ResidueField R₁) (ResidueField R₂) :=
    Algebra.isSeparable_tower_top_of_isSeparable K (ResidueField R₁) (ResidueField R₂)
  exact IsSepClosed.algebraMap_bijective (ResidueField R₁) (ResidueField R₂)

/-- **The residue field of a strict henselization is separable over the residue field of the
base**, for the extension induced by the structure map: it is identified with the given separable
closure compatibly with the residue maps. -/
theorem isSeparable_residueField_of_isHenselization {A : Type u} [CommRing A] [IsLocalRing A]
    {L : Type v} [Field L] [Algebra (ResidueField A) L] [IsSepClosure (ResidueField A) L]
    {Rh : Type w} [CommRing Rh] [IsLocalRing Rh] [Algebra A Rh]
    [IsLocalRing.IsHenselization A L Rh] :
    letI := IsLocalRing.IsHenselization.isLocalHom (R := A) (L := L) (Rh := Rh)
    letI := (ResidueField.map (algebraMap A Rh)).toAlgebra
    Algebra.IsSeparable (ResidueField A) (ResidueField Rh) := by
  let := IsLocalRing.IsHenselization.isLocalHom (R := A) (L := L) (Rh := Rh)
  let := (ResidueField.map (algebraMap A Rh)).toAlgebra
  obtain ⟨e, he⟩ := IsLocalRing.IsHenselization.exists_residueFieldEquiv (R := A) (L := L)
    (Rh := Rh)
  let φ : ResidueField Rh →ₐ[ResidueField A] L :=
    { e.symm.toRingHom with
      commutes' := fun c ↦ by
        obtain ⟨a, rfl⟩ := residue_surjective c
        show e.symm (ResidueField.map (algebraMap A Rh) (residue A a)) = _
        rw [ResidueField.map_residue, ← he a, RingEquiv.symm_apply_apply] }
  exact Algebra.IsSeparable.of_algHom (ResidueField A) L φ

end StacksDraft

end
