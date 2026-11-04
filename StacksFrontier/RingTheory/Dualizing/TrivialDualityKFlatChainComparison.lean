module

public import StacksFrontier.RingTheory.Dualizing.TrivialDualityKFlat
public import StacksFrontier.RingTheory.Dualizing.TrivialDualityKFlatNatTrans

/-!
# The remaining content of Stacks 0BZE, with the change-of-rings bundle eliminated

`StacksFrontier/RingTheory/Dualizing/TrivialDualityKFlat.lean` reduces Stacks 0BZE to a family of
isomorphisms on the K-flat complexes, natural in chain maps between them, between derived
coextension of scalars `RHom_R(A, -)` and the derived tensor product functor `(bundle f).F` of
Stacks 06Y6. The tensor side of that comparison is a *field of a structure obtained by
`Classical.choice`*: `CochainComplex.DerivedTensor.canonicalDerivedTensorChangeOfRings` is
`Classical.choice` applied to a `Nonempty` witness, so none of its fields reduce — not even with
`import all` — and `(bundle f).F`, `(bundle f).directTensor` and `(bundle f).commShift` are
opaque constants about which only the structure's own propositional fields may be used.

This file removes the bundle from the remaining obligation. Two of those propositional fields are
exactly what is needed:

* `isIso_alphaF` says the counit `alphaF.app K : F(Q K) ⟶ Q(directTensor K)` is invertible at a
  K-flat complex `K`;
* `directTensorComparison` identifies `directTensor` with the *concrete* functor
  `extendScalarsLarge f ⋙ tensorRightLarge (dualComplex f)`, that is, `K ↦ (A ⊗_R K) ⊗_A ω` for
  `ω = RHom_R(A, R)` read on the chosen representative.

Composing the two gives `Stacks0BZE.bundleObjIso`, a chain-level computation of the derived
tensor product at a K-flat complex, natural in chain maps. Consequently Stacks 0BZE follows from
a family of isomorphisms

`RHom_R(A, Q K) ≅ Q((A ⊗_R K) ⊗_A ω)`

in `D(A)`, for `K` K-flat, natural in chain maps between such complexes — a statement in which no
field of the change-of-rings bundle occurs, and which asks for no compatibility with the shift.

## Main definitions

* `Stacks0BZE.chainDirectTensor` — the concrete functor `K ↦ (A ⊗_R K) ⊗_A ω` on cochain
  complexes.
* `Stacks0BZE.bundleObjIso` — the derived tensor product of Stacks 06Y6, computed at a K-flat
  complex by `Stacks0BZE.chainDirectTensor`.
* `Stacks0BZE.cardIsoOfChainLevelIso` — **Stacks 0BZE from a chain-level natural family**, as an
  isomorphism of functors.

## Main results

* `Stacks0BZE.bundleObjIso_naturality` — that computation is natural in chain maps.
* `Stacks0BZE.card_of_chainLevelIso` — Stacks 0BZE from a chain-level natural family, in the
  shape `Stacks0BZE.card_of_isIso_comparison` is stated at, which is the shape the consumers of
  the tag in the upper-shriek development ask for.

## Implementation notes

The family asked for here is *not* required to realize `Stacks0BZE.comparison`; like
`Stacks0BZE.card_of_kFlatComparison` and unlike `Stacks0BZE.cardIso`, it is an arbitrary natural
family. That is what makes the obligation shift-free: the descent
`ModuleSystemRlimTensor.natIsoOfResolutions` consumes naturality in chain maps between members of
the resolving class and nothing else, whereas the compact-generator dévissage of
`StacksFrontier/Homology/Devissage/` would need `CategoryTheory.NatTrans.CommShift` for the
comparison against `(bundle f).commShift`, which is an opaque constant carrying no coherence with
`alphaF` at all.

## References

* [The Stacks Project, Tag 0BZE](https://stacks.math.columbia.edu/tag/0BZE)
* [The Stacks Project, Tag 0A70](https://stacks.math.columbia.edu/tag/0A70)
* [The Stacks Project, Tag 06Y6](https://stacks.math.columbia.edu/tag/06Y6)
-/

@[expose] public noncomputable section

open CategoryTheory

attribute [local instance 10000] HasDerivedCategory.standard

universe u v

namespace Stacks0BZE

variable {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A)

/-- The concrete chain-level derived tensor factor: extension of scalars along `f` followed by
tensoring over `A` with the chosen representative `Stacks0BZE.dualComplex` of `RHom_R(A, R)`.
This is the functor `K ↦ (A ⊗_R K) ⊗_A ω` on cochain complexes of `R`-modules, and the field
`directTensorComparison` of the change-of-rings bundle identifies the bundle's own opaque
`directTensor` with it. -/
abbrev chainDirectTensor :
    CochainComplex (ModuleCat.{max v u} R) ℤ ⥤ CochainComplex (ModuleCat.{max v u} A) ℤ :=
  CochainComplex.extendScalarsLarge.{v} f ⋙
    CochainComplex.tensorRightLarge.{u, max v u} (dualComplex.{u, v} f)

/-- **The derived tensor product of Stacks 06Y6, computed at a K-flat complex.** The counit
`alphaF` of the change-of-rings bundle is invertible at a K-flat complex, and
`directTensorComparison` identifies the bundle's direct tensor construction with the concrete
functor `Stacks0BZE.chainDirectTensor`; so at a K-flat complex `K` the value of the opaque functor
`(bundle f).F` is the class of `(A ⊗_R K) ⊗_A ω`. -/
def bundleObjIso (K : CochainComplex (ModuleCat.{max v u} R) ℤ)
    (hK : CochainComplex.KFlat.{u, max v u} K) :
    (bundle.{u, v} f).F.obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj ((chainDirectTensor.{u, v} f).obj K) :=
  letI := (bundle.{u, v} f).isIso_alphaF K hK
  asIso ((bundle.{u, v} f).alphaF.app K) ≪≫
    DerivedCategory.Q.mapIso ((bundle.{u, v} f).directTensorComparison.app K)

/-- The forward map of `Stacks0BZE.bundleObjIso` is the counit component `alphaF.app K` followed
by the image under `DerivedCategory.Q` of the component at `K` of `directTensorComparison`. -/
lemma bundleObjIso_hom (K : CochainComplex (ModuleCat.{max v u} R) ℤ)
    (hK : CochainComplex.KFlat.{u, max v u} K) :
    (bundleObjIso.{u, v} f K hK).hom =
      (bundle.{u, v} f).alphaF.app K ≫
        DerivedCategory.Q.map ((bundle.{u, v} f).directTensorComparison.hom.app K) :=
  rfl

/-- `Stacks0BZE.bundleObjIso` is natural in chain maps: both of its legs are components of
natural transformations. -/
theorem bundleObjIso_naturality {K L : CochainComplex (ModuleCat.{max v u} R) ℤ}
    (hK : CochainComplex.KFlat.{u, max v u} K) (hL : CochainComplex.KFlat.{u, max v u} L)
    (g : K ⟶ L) :
    (bundle.{u, v} f).F.map (DerivedCategory.Q.map g) ≫ (bundleObjIso.{u, v} f L hL).hom =
      (bundleObjIso.{u, v} f K hK).hom ≫
        DerivedCategory.Q.map ((chainDirectTensor.{u, v} f).map g) := by
  have ha : (bundle.{u, v} f).F.map (DerivedCategory.Q.map g) ≫
        (bundle.{u, v} f).alphaF.app L =
      (bundle.{u, v} f).alphaF.app K ≫
        DerivedCategory.Q.map ((bundle.{u, v} f).directTensor.map g) :=
    (bundle.{u, v} f).alphaF.naturality g
  have hc : (bundle.{u, v} f).directTensor.map g ≫
        (bundle.{u, v} f).directTensorComparison.hom.app L =
      (bundle.{u, v} f).directTensorComparison.hom.app K ≫ (chainDirectTensor.{u, v} f).map g :=
    (bundle.{u, v} f).directTensorComparison.hom.naturality g
  rw [bundleObjIso_hom, bundleObjIso_hom, ← Category.assoc, ha, Category.assoc, Category.assoc,
    ← Functor.map_comp, hc, Functor.map_comp]

/-- Every cochain complex of `R`-modules is resolved by a K-flat one: this is
`Stacks0BZE.kFlat_resolves`. -/
alias kFlat_resolution := Stacks0BZE.kFlat_resolves

/-- **Stacks 0BZE from a chain-level natural family.** A family of isomorphisms
`RHom_R(A, Q K) ≅ Q((A ⊗_R K) ⊗_A RHom_R(A, R))` in `D(A)`, indexed by the K-flat complexes `K`
and natural in chain maps between them, is enough: the K-flat complexes resolve every complex, and
the derived tensor product of Stacks 06Y6 is computed on them by `Stacks0BZE.bundleObjIso`.

The family is not required to realize `Stacks0BZE.comparison`, and no compatibility with the shift
is asked for. -/
def cardIsoOfChainLevelIso
    (e : ∀ K : CochainComplex (ModuleCat.{max v u} R) ℤ, CochainComplex.KFlat.{u, max v u} K →
      ((Dualizing.derivedHom.{u, v} f).obj (DerivedCategory.Q.obj K) ≅
        DerivedCategory.Q.obj ((chainDirectTensor.{u, v} f).obj K)))
    (he : ∀ (K L : CochainComplex (ModuleCat.{max v u} R) ℤ)
      (hK : CochainComplex.KFlat.{u, max v u} K) (hL : CochainComplex.KFlat.{u, max v u} L)
      (g : K ⟶ L),
      (Dualizing.derivedHom.{u, v} f).map (DerivedCategory.Q.map g) ≫ (e L hL).hom =
        (e K hK).hom ≫ DerivedCategory.Q.map ((chainDirectTensor.{u, v} f).map g)) :
    Dualizing.derivedHom.{u, v} f ≅ (bundle.{u, v} f).F :=
  ModuleSystemRlimTensor.natIsoOfResolutions
    (B := ModuleCat.{max v u} R) (fun K => CochainComplex.KFlat.{u, max v u} K)
    kFlat_resolution.{u, v} _ _
    (fun K hK => e K hK ≪≫ (bundleObjIso.{u, v} f K hK).symm)
    (fun K L hK hL g => by
      have hb := bundleObjIso_naturality.{u, v} f hK hL g
      simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
      rw [← Category.assoc, he K L hK hL g, Category.assoc]
      congr 1
      symm
      rw [Iso.inv_comp_eq, ← Category.assoc, ← hb, Category.assoc, Iso.hom_inv_id,
        Category.comp_id])

/-- **Stacks 0BZE from a chain-level natural family**, in the shape
`Stacks0BZE.card_of_isIso_comparison` is stated at: the shape the upper-shriek development's
carriers of the tag consume. -/
theorem card_of_chainLevelIso
    (hperfect : letI := f.toAlgebra
      StacksDraft.Perfect.IsPerfectModule (R := R) A)
    (hcomp : ∃ e : ∀ K : CochainComplex (ModuleCat.{max v u} R) ℤ,
        CochainComplex.KFlat.{u, max v u} K →
          ((Dualizing.derivedHom.{u, v} f).obj (DerivedCategory.Q.obj K) ≅
            DerivedCategory.Q.obj ((chainDirectTensor.{u, v} f).obj K)),
      ∀ (K L : CochainComplex (ModuleCat.{max v u} R) ℤ)
        (hK : CochainComplex.KFlat.{u, max v u} K) (hL : CochainComplex.KFlat.{u, max v u} L)
        (g : K ⟶ L),
        (Dualizing.derivedHom.{u, v} f).map (DerivedCategory.Q.map g) ≫ (e L hL).hom =
          (e K hK).hom ≫ DerivedCategory.Q.map ((chainDirectTensor.{u, v} f).map g)) :
    letI : MonoidalCategoryStruct (ModuleCat.{max v u} R) :=
      ModuleCat.liftedModuleMonoidalStruct.{u, max v u}
    letI : MonoidalCategory (ModuleCat.{max v u} R) :=
      ModuleCat.liftedModuleMonoidal.{u, max v u}
    let R₀ := (DerivedCategory.singleFunctor (ModuleCat.{max v u} R) 0).obj
      (MonoidalCategoryStruct.tensorUnit (ModuleCat.{max v u} R))
    Nonempty (Dualizing.derivedHom.{u, v} f ≅
      (CochainComplex.DerivedTensor.canonicalDerivedTensorChangeOfRings f
        ((DerivedCategory.Qh (C := ModuleCat.{max v u} A)).objPreimage
          ((Dualizing.derivedHom.{u, v} f).obj R₀)).as).F) := by
  intro R₀
  have := hperfect
  obtain ⟨e, he⟩ := hcomp
  exact ⟨cardIsoOfChainLevelIso.{u, v} f e he⟩

end Stacks0BZE

end
