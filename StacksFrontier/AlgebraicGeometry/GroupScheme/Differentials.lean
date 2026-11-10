module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import StacksFrontier.AlgebraicGeometry.ConormalSequenceSplit.ShortExact
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.Transport
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.FiniteType
public import StacksCore.Tactic.StacksAttribute

/-!
# The sheaf of relative differentials of a group scheme

Let `G` be a group scheme over a scheme `S` with structure morphism `f : G ⟶ S`,
multiplication `m` and identity section `e`.  The sheaf of relative differentials of `G` over
`S` is pulled back from the base: there are canonical isomorphisms
`Ω_{G/S} ≅ f^*𝒞_{S/G} ≅ f^*e^*Ω_{G/S}`, where `𝒞_{S/G}` is the conormal sheaf of `e`.  Over a
field the pulled-back factor is a vector space, so `Ω_{G/S}` is a free module.

## Main definitions

* `AlgebraicGeometry.GroupSchemeDifferentials.mul`,
  `AlgebraicGeometry.GroupSchemeDifferentials.identity` and
  `AlgebraicGeometry.GroupSchemeDifferentials.unitSection` are the multiplication, the identity
  section and the morphism `(e ∘ f, 1) : G ⟶ G ×_S G`, read off the group object structure of
  `Over.mk f`.
* `AlgebraicGeometry.GroupSchemeDifferentials.shearIso` is the shearing automorphism
  `(g, h) ↦ (m(g, h), h)` of `G ×_S G` over `G`.
* `AlgebraicGeometry.GroupSchemeDifferentials.shearDifferentialsIso` is the resulting
  identification `m^*Ω_{G/S} ≅ pr₀^*Ω_{G/S}`.
* `AlgebraicGeometry.GroupSchemeDifferentials.conormalIsoPullbackIdentity` is the isomorphism
  `𝒞_{S/G} ≅ e^*Ω_{G/S}` given by the first arrow of the conormal sequence of `e`.

## Main results

* `AlgebraicGeometry.GroupSchemeDifferentials.isPullback_mul`: multiplication and the second
  projection exhibit `G ×_S G` as a fibre product of `f` with itself.
* `AlgebraicGeometry.GroupSchemeDifferentials.relativeDifferentialsIsoPullbackConormal` and
  `AlgebraicGeometry.GroupSchemeDifferentials.pullbackConormalIsoPullbackIdentity`: the chain of
  canonical isomorphisms `Ω_{G/S} ≅ f^*𝒞_{S/G} ≅ f^*e^*Ω_{G/S}`.
* `AlgebraicGeometry.GroupSchemeDifferentials.relativeDifferentialsIsoPullbackIdentity`: their
  composite `Ω_{G/S} ≅ f^*e^*Ω_{G/S}`.
* `AlgebraicGeometry.GroupSchemeDifferentials.exists_free_iso_relativeDifferentials_of_field`:
  over a field `Ω_{G/S}` is a free `𝒪_G`-module.

## References

* [Stacks Project, Tag 047I](https://stacks.math.columbia.edu/tag/047I)
* [BookAV, Proposition 3.15]
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.MonoidalCategory

universe u

namespace AlgebraicGeometry.GroupSchemeDifferentials

open AlgebraicGeometry.Scheme.Hom

variable {S G : Scheme.{u}} (f : G ⟶ S) [GrpObj (Over.mk f)]

/-- The multiplication of a group scheme as a morphism of schemes `G ×_S G ⟶ G`. -/
noncomputable def mul : pullback f f ⟶ G := (μ[Over.mk f]).left

/-- The identity section of a group scheme as a morphism of schemes `S ⟶ G`. -/
noncomputable def identity : S ⟶ G := (η[Over.mk f]).left

/-- The identity section is a section of the structure morphism. -/
@[simp]
lemma identity_comp : identity f ≫ f = 𝟙 S := (η[Over.mk f]).w

/-- Multiplication is a morphism over `S`, written against the second projection. -/
lemma mul_comp : mul f ≫ f = pullback.snd f f ≫ f := by
  have hw := (μ[Over.mk f]).w
  simp only [Over.tensorObj_hom, Over.mk_hom] at hw
  rw [show mul f = (μ[Over.mk f]).left from rfl, hw, pullback.condition]

/-- **The shearing automorphism** `(g, h) ↦ (m(g, h), h)` of `G ×_S G`, as an automorphism of
`(Over.mk f) ⊗ (Over.mk f)` in the category of schemes over `S`.  Its inverse is
`(g, h) ↦ (g h⁻¹, h)`. -/
@[sga "3 VIA 0.1" "partial"]
noncomputable def shearIso : (Over.mk f ⊗ Over.mk f) ≅ (Over.mk f ⊗ Over.mk f) where
  hom := lift μ[Over.mk f] (snd _ _)
  inv := lift (fst _ _ / snd _ _) (snd _ _)
  hom_inv_id := by apply hom_ext <;> simp [GrpObj.comp_div, MonObj.mul_eq_mul]
  inv_hom_id := by apply hom_ext <;> simp [MonObj.comp_mul, MonObj.mul_eq_mul]

/-- **Multiplication and the second projection exhibit `G ×_S G` as a fibre product of `f` with
itself.** -/
@[sga "3 VIA 0.1" "partial"]
lemma isPullback_mul : IsPullback (mul f) (pullback.snd f f) f f := by
  refine IsPullback.of_iso_pullback ⟨mul_comp f⟩ ((Over.forget S).mapIso (shearIso f)) ?_ ?_
  · change ((shearIso f).hom ≫ fst (Over.mk f) (Over.mk f)).left = _
    simp [shearIso, mul]
  · change ((shearIso f).hom ≫ snd (Over.mk f) (Over.mk f)).left = _
    simp [shearIso]

/-- The morphism `(e ∘ f, 1) : G ⟶ G ×_S G`. -/
noncomputable def unitSection : G ⟶ pullback f f :=
  (lift (toUnit (Over.mk f) ≫ η[Over.mk f]) (𝟙 (Over.mk f))).left

/-- The composite of `(e ∘ f, 1)` with multiplication is the identity. -/
@[simp]
lemma unitSection_mul : unitSection f ≫ mul f = 𝟙 G := by
  change (lift (toUnit (Over.mk f) ≫ η[Over.mk f]) (𝟙 (Over.mk f)) ≫ μ[Over.mk f]).left = _
  rw [MonObj.lift_comp_one_left]
  rfl

/-- The first component of `(e ∘ f, 1)` is `e ∘ f`. -/
@[simp]
lemma unitSection_fst : unitSection f ≫ pullback.fst f f = f ≫ identity f := by
  change (lift (toUnit (Over.mk f) ≫ η[Over.mk f]) (𝟙 (Over.mk f)) ≫ fst _ _).left = _
  simp [identity]

/-- The second component of `(e ∘ f, 1)` is the identity. -/
@[simp]
lemma unitSection_snd : unitSection f ≫ pullback.snd f f = 𝟙 G := by
  change (lift (toUnit (Over.mk f) ≫ η[Over.mk f]) (𝟙 (Over.mk f)) ≫ snd _ _).left = _
  simp

/-- **The shearing comparison on relative differentials**, `m^*Ω_{G/S} ≅ pr₀^*Ω_{G/S}`.  Both
sides are identified with `Ω_{(G ×_S G)/G}` by the base change isomorphism of
[Stacks, Tag 01V0], applied to the cartesian square of `isPullback_mul` and to the standard
pullback square. -/
noncomputable def shearDifferentialsIso :
    (Scheme.Modules.pullback (mul f)).obj (relativeDifferentials f) ≅
      (Scheme.Modules.pullback (pullback.fst f f)).obj (relativeDifferentials f) :=
  haveI : IsIso (relativeDifferentialsMap (mul f) f (pullback.snd f f) f (isPullback_mul f).w) :=
    isIso_relativeDifferentialsMap_of_isPullback (mul f) (pullback.snd f f) f f (isPullback_mul f)
  haveI : IsIso (relativeDifferentialsMap (pullback.fst f f) f (pullback.snd f f) f
      (IsPullback.of_hasPullback f f).w) :=
    isIso_relativeDifferentialsMap_of_isPullback (pullback.fst f f) (pullback.snd f f) f f
      (IsPullback.of_hasPullback f f)
  (asIso (relativeDifferentialsMap (mul f) f (pullback.snd f f) f (isPullback_mul f).w)).trans
    (asIso (relativeDifferentialsMap (pullback.fst f f) f (pullback.snd f f) f
      (IsPullback.of_hasPullback f f).w)).symm

/-- **The canonical isomorphism `Ω_{G/S} ≅ f^*e^*Ω_{G/S}`.**  The sheaf of relative
differentials of a group scheme is the inverse image of its restriction along the identity
section. -/
@[stacks 047I "the composite Ω_{G/S} ≅ f^*e^*Ω_{G/S} of the chain of isomorphisms",
  sga "3 II 4.11.4" "(a)"]
noncomputable def relativeDifferentialsIsoPullbackIdentity :
    relativeDifferentials f ≅
      (Scheme.Modules.pullback f).obj
        ((Scheme.Modules.pullback (identity f)).obj (relativeDifferentials f)) :=
  ((Scheme.Modules.pullbackId G).app (relativeDifferentials f)).symm ≪≫
  (Scheme.Modules.pullbackCongr (unitSection_mul f).symm).app (relativeDifferentials f) ≪≫
  ((Scheme.Modules.pullbackComp (unitSection f) (mul f)).app (relativeDifferentials f)).symm ≪≫
  (Scheme.Modules.pullback (unitSection f)).mapIso (shearDifferentialsIso f) ≪≫
  (Scheme.Modules.pullbackComp (unitSection f) (pullback.fst f f)).app
    (relativeDifferentials f) ≪≫
  (Scheme.Modules.pullbackCongr (unitSection_fst f)).app (relativeDifferentials f) ≪≫
  ((Scheme.Modules.pullbackComp f (identity f)).app (relativeDifferentials f)).symm

/-- The identity section of a group scheme is an immersion. -/
@[ega "IV 16.2.3" "special case"]
instance isImmersion_identity : IsImmersion (identity f) :=
  Stacks.ConormalSequenceSplit.isImmersion_of_section f (identity f) (identity_comp f)

/-- **The conormal sheaf of the identity section**, `𝒞_{S/G} ≅ e^*Ω_{G/S}`: the first arrow of the
conormal sequence of the immersion `e`, which is an isomorphism because `e` is a section of `f`
([Stacks, Tag 0474]). -/
noncomputable def conormalIsoPullbackIdentity :
    (Stacks.AlgebraicGeometry.RegularIdealSheaf.conormalSheaf (identity f) : S.Modules) ≅
      (Scheme.Modules.pullback (identity f)).obj (relativeDifferentials f) :=
  haveI := Stacks.ConormalSequenceSplit.isIso_conormalDifferential_of_section f (identity f)
    (identity_comp f)
  asIso (Stacks.ConormalSequenceRight.conormalDifferential (identity f) f)

/-- The isomorphism `𝒞_{S/G} ≅ e^*Ω_{G/S}` is the first arrow of the conormal sequence of `e`. -/
@[simp]
lemma conormalIsoPullbackIdentity_hom :
    (conormalIsoPullbackIdentity f).hom =
      Stacks.ConormalSequenceRight.conormalDifferential (identity f) f :=
  rfl

/-- **The second isomorphism of the chain**, `f^*𝒞_{S/G} ≅ f^*e^*Ω_{G/S}`,
where `𝒞_{S/G}` is the conormal sheaf of the identity section `e`: the inverse image along `f`
of `conormalIsoPullbackIdentity`, that is, of the first arrow `𝒞_{S/G} ⟶ e^*Ω_{G/S}` of the
conormal sequence of `e`. -/
@[stacks 047I "the second isomorphism of the chain, f^*𝒞_{S/G} ≅ f^*e^*Ω_{G/S}, where 𝒞_{S/G}
is the conormal sheaf of the identity section e: f^* of the first arrow of the conormal sequence
of e, an isomorphism by Tag 0474"]
noncomputable def pullbackConormalIsoPullbackIdentity :
    (Scheme.Modules.pullback f).obj
        (Stacks.AlgebraicGeometry.RegularIdealSheaf.conormalSheaf (identity f) : S.Modules) ≅
      (Scheme.Modules.pullback f).obj
        ((Scheme.Modules.pullback (identity f)).obj (relativeDifferentials f)) :=
  (Scheme.Modules.pullback f).mapIso (conormalIsoPullbackIdentity f)

/-- **The first isomorphism of the chain**, `Ω_{G/S} ≅ f^*𝒞_{S/G}`, where
`𝒞_{S/G}` is the conormal sheaf of the identity section `e`: the shearing isomorphism
`Ω_{G/S} ≅ f^*e^*Ω_{G/S}` followed by the inverse of `pullbackConormalIsoPullbackIdentity`. -/
@[stacks 047I "the first isomorphism of the chain, Ω_{G/S} ≅ f^*𝒞_{S/G}, where 𝒞_{S/G} is the
conormal sheaf of the identity section e"]
noncomputable def relativeDifferentialsIsoPullbackConormal :
    relativeDifferentials f ≅
      (Scheme.Modules.pullback f).obj
        (Stacks.AlgebraicGeometry.RegularIdealSheaf.conormalSheaf (identity f) : S.Modules) :=
  relativeDifferentialsIsoPullbackIdentity f ≪≫ (pullbackConormalIsoPullbackIdentity f).symm

/-- The two isomorphisms of the chain `Ω_{G/S} ≅ f^*𝒞_{S/G} ≅ f^*e^*Ω_{G/S}` compose to the
shearing isomorphism `relativeDifferentialsIsoPullbackIdentity`. -/
@[simp]
lemma relativeDifferentialsIsoPullbackConormal_trans :
    relativeDifferentialsIsoPullbackConormal f ≪≫ pullbackConormalIsoPullbackIdentity f =
      relativeDifferentialsIsoPullbackIdentity f := by
  simp [relativeDifferentialsIsoPullbackConormal]

/-- **A quasi-coherent module on the spectrum of a field is free.** -/
theorem exists_free_iso_of_isQuasicoherent_spec_field (k : Type u) [Field k]
    (N : (Spec (CommRingCat.of k)).Modules) [N.IsQuasicoherent] :
    ∃ I : Type u,
      Nonempty (N ≅ SheafOfModules.free (R := (Spec (CommRingCat.of k)).ringCatSheaf) I) := by
  let R : CommRingCat.{u} := CommRingCat.of k
  let V : ModuleCat.{u} R := (modulesSpecToSheaf.obj N).presheaf.obj (.op ⊤)
  let _ : Field (R : Type u) := inferInstanceAs (Field k)
  let b := Module.Basis.ofVectorSpace (R : Type u) (V : Type u)
  refine ⟨Module.Basis.ofVectorSpaceIndex (R : Type u) (V : Type u), ⟨?_⟩⟩
  exact (asIso N.fromTildeΓ).symm ≪≫ (tilde.functor R).mapIso b.repr.toModuleIso ≪≫
    tildeFinsupp _

/-- **Freeness over a field.**  If the base is the spectrum of a field, the sheaf of relative
differentials of a group scheme is a free `𝒪_G`-module. -/
@[stacks 047I "freeness over a field", sga "3 II 4.11.4" "(a) over a field"]
theorem exists_free_iso_relativeDifferentials_of_field (k : Type u) [Field k] (G : Scheme.{u})
    (f : G ⟶ Spec (CommRingCat.of k)) [GrpObj (Over.mk f)] :
    ∃ I : Type u,
      Nonempty (relativeDifferentials f ≅
        SheafOfModules.free (R := G.ringCatSheaf) I) := by
  obtain ⟨I, ⟨e⟩⟩ := exists_free_iso_of_isQuasicoherent_spec_field k
    ((Scheme.Modules.pullback (identity f)).obj (relativeDifferentials f))
  exact ⟨I, ⟨relativeDifferentialsIsoPullbackIdentity f ≪≫
    (Scheme.Modules.pullback f).mapIso e ≪≫ Scheme.Modules.pullbackFreeIso f I⟩⟩

end AlgebraicGeometry.GroupSchemeDifferentials

end
