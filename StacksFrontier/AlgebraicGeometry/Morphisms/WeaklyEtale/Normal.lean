module

public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.Stalks
public import StacksFrontier.AlgebraicGeometry.Properties.Normal
public import StacksFrontier.RingTheory.Henselian.PermanenceOfProperties

/-!
# Normality ascends along a weakly étale morphism

The source of a weakly étale morphism of schemes is normal as soon as its target is.

## Main results

* `AlgebraicGeometry.isNormal_of_weaklyEtale` is Stacks Tag 0950: for a weakly étale
  `f : X ⟶ Y` with `Y` normal, `X` is normal.

## Implementation notes

Normality is checked stalkwise, by `AlgebraicGeometry.isNormal_iff_stalk_normal`, and at a point
`x` of `X` it is transported through strict henselizations. Choose strict henselizations `Ysh` of
`𝒪_{Y, f x}` and `Xsh` of `𝒪_{X, x}` in the common universe, with
`IsLocalRing.exists_isHenselization_separableClosure`. Normality of a local ring is equivalent to
normality of its strict henselization, which is Stacks Tag 06DI in the form
`isNormalDomain_tfae_henselization_strictHenselization`, so it suffices to carry normality from
`Ysh` to `Xsh`. The residue field of `Xsh` is separably closed, so the separably closed field
`ResidueField Ysh` embeds into it over the residue field of `𝒪_{Y, f x}`; the universal property
of the henselization `Ysh` lifts that embedding to a local `𝒪_{Y, f x}`-algebra map
`Ysh → Xsh` compatible with the residue maps, and Stacks Tag 094Z says that map is bijective.
Normality then transports along the resulting ring isomorphism.

The strict henselization of `𝒪_{Y, f x}` with respect to the separable closure of its residue
field is produced first with the *separable closure itself* as prescribed residue extension, and
`IsLocalRing.IsHenselization.exists_residueFieldAlgebra` then replaces that prescription by the
residue field of `Ysh`, which is what both Tag 06DI and Tag 094Z consume.

## References

* [Stacks Project, Tag 0950](https://stacks.math.columbia.edu/tag/0950)
* [Stacks Project, Tag 094Z](https://stacks.math.columbia.edu/tag/094Z)
* [Stacks Project, Tag 06DI](https://stacks.math.columbia.edu/tag/06DI)
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u

namespace AlgebraicGeometry

/-- A local ring is a normal domain iff its strict henselization is. -/
private theorem isNormalDomain_iff_of_isHenselization_separableClosure (R Rsh : Type u)
    [CommRing R] [CommRing Rsh] [IsLocalRing R] [IsLocalRing Rsh] [Algebra R Rsh]
    [IsHenselization R (SeparableClosure (ResidueField R)) Rsh] :
    (IsDomain R ∧ IsIntegrallyClosed R) ↔ (IsDomain Rsh ∧ IsIntegrallyClosed Rsh) := by
  obtain ⟨Rh, _, _, _, _⟩ := exists_isHenselization_residueField R
  exact (isNormalDomain_tfae_henselization_strictHenselization R Rh Rsh
    (SeparableClosure (ResidueField R))).out 1 3

/-- **Stacks Project, Tag 0950.** A weakly étale morphism with normal target has normal
source. -/
@[stacks 0950]
theorem isNormal_of_weaklyEtale {X Y : Scheme.{u}} (f : X ⟶ Y) [IsNormal Y] [WeaklyEtale f] :
    IsNormal X := by
  rw [isNormal_iff_stalk_normal]
  intro x
  let R := Y.presheaf.stalk (f x)
  let S := X.presheaf.stalk x
  let : Algebra R S := (f.stalkMap x).hom.toAlgebra
  obtain ⟨hR, hnR⟩ := (isNormal_iff_stalk_normal Y).mp inferInstance (f x)
  let : IsDomain R := hR
  obtain ⟨Ysh, _, _, _, hYsh⟩ := exists_isHenselization_separableClosure R
  obtain ⟨Xsh, _, _, _, hXsh⟩ := exists_isHenselization_separableClosure S
  let := hYsh
  let := hXsh
  obtain ⟨algResY, hYsh', hsepY, hresY⟩ :=
    IsHenselization.exists_residueFieldAlgebra
      (R := R) (L := SeparableClosure (ResidueField R)) (Rh := Ysh)
  let := algResY
  let := hYsh'
  have : IsSepClosure (ResidueField R) (ResidueField Ysh) := hsepY inferInstance
  obtain ⟨_, _⟩ : IsDomain Ysh ∧ IsIntegrallyClosed Ysh :=
    (isNormalDomain_iff_of_isHenselization_separableClosure R Ysh).mp ⟨hR, hnR⟩
  have : IsLocalHom (algebraMap S Xsh) :=
    IsHenselization.isLocalHom (R := S) (L := SeparableClosure (ResidueField S))
  let : Algebra R Xsh := ((algebraMap S Xsh).comp (f.stalkMap x).hom).toAlgebra
  let : IsScalarTower R S Xsh := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsLocalHom (algebraMap R Xsh) :=
    RingHom.isLocalHom_comp (algebraMap S Xsh) (f.stalkMap x).hom
  obtain ⟨algResX, hXsh', hsepX, -⟩ :=
    IsHenselization.exists_residueFieldAlgebra
      (R := S) (L := SeparableClosure (ResidueField S)) (Rh := Xsh)
  let := algResX
  let := hXsh'
  have : IsSepClosure (ResidueField S) (ResidueField Xsh) := hsepX inferInstance
  have : IsSepClosed (ResidueField Xsh) := IsSepClosure.sep_closed (ResidueField S)
  let : Algebra (ResidueField R) (ResidueField Xsh) :=
    (ResidueField.map (algebraMap R Xsh)).toAlgebra
  let φ : ResidueField Ysh →ₐ[ResidueField R] ResidueField Xsh := IsSepClosed.lift
  have hφ : φ.toRingHom.comp ((residue Ysh).comp (algebraMap R Ysh)) =
      (residue Xsh).comp (algebraMap R Xsh) := by
    ext a
    show φ (residue Ysh (algebraMap R Ysh a)) = residue Xsh (algebraMap R Xsh a)
    rw [← hresY a, φ.commutes]
    exact ResidueField.map_residue (algebraMap R Xsh) a
  have : HenselianLocalRing Xsh :=
    IsHenselization.henselian (R := S) (L := ResidueField Xsh)
  obtain ⟨g, hg, hgres⟩ :=
    (StacksDraft.existsUnique_isLocalHom_comp_residue_of_indEtale
      (IsHenselization.ind_etale (R := R) (L := ResidueField Ysh) (Rh := Ysh))
      φ.toRingHom hφ).exists
  have hbij : Function.Bijective g.toRingHom :=
    (weaklyEtale_iff_strictHenselizationMap_bijective f).mp inferInstance
      x Ysh Xsh φ.toRingHom g.toRingHom ⟨fun a ha ↦ hg.map_nonunit a ha⟩
      (by ext a; exact g.commutes a) hgres
  let e : Ysh ≃+* Xsh := RingEquiv.ofBijective g.toRingHom hbij
  obtain ⟨_, hS⟩ : IsDomain S ∧ IsIntegrallyClosed S :=
    (isNormalDomain_iff_of_isHenselization_separableClosure S Xsh).mpr
      ⟨Function.Injective.isDomain e.symm e.symm.injective, IsIntegrallyClosed.of_equiv e⟩
  exact ⟨inferInstance, hS⟩

end AlgebraicGeometry

end
