module

public import Mathlib.Algebra.Algebra.Hom.Rat
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.Normal.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringSieveDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupActionRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyInjective
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteLocalSurjectivity
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.IrreducibleGaloisAction
public import StacksFrontier.FieldTheory.AlgClosedFiniteExtension

/-!
# The quotient of the spectrum of the algebraic closure of the rationals by its Galois group

The absolute Galois group of `ℚ` acts on the one-point scheme `Spec ℚ̄` over `Spec ℚ`, and
the action is faithful on the residue field at that point. Its fppf sheaf quotient is
therefore an algebraic space over `Spec ℚ` which is not a scheme. An algebraic extension of
`ℚ` carrying a point of that quotient is either algebraically closed or a real closure
of `ℚ`.

## Main definitions

* `AlgebraicGeometry.RationalGaloisQuotient.base` is `Spec ℚ` and
  `AlgebraicGeometry.RationalGaloisQuotient.cover` is `Spec ℚ̄` over it, with
  `AlgebraicGeometry.RationalGaloisQuotient.siteCover` the latter as an object of a big
  fppf site over the former.
* `AlgebraicGeometry.RationalGaloisQuotient.galoisAction` is the action of
  `AlgebraicGeometry.RationalGaloisQuotient.galoisGroup`, the absolute Galois group of `ℚ`.
* `AlgebraicGeometry.RationalGaloisQuotient.galoisQuotient` is the fppf sheaf quotient, and
  `AlgebraicGeometry.RationalGaloisQuotient.galoisQuotientToBase` is its structure morphism
  to `Spec ℚ`.

## Main results

* `AlgebraicGeometry.Scheme.spec_hom_eq_id_of_residueFieldMap_eq_congr`: an endomorphism of
  the spectrum of a field which fixes a point and induces the canonical map on the residue
  field there is the identity.
* `AlgebraicGeometry.RationalGaloisQuotient.galoisAction_nontrivialOnFixedResidueFields`:
  every nonidentity element of the Galois group acts nontrivially on the residue field at
  the unique point of `Spec ℚ̄`.
* `AlgebraicGeometry.RationalGaloisQuotient.fieldPoint_algEquiv_algebraicClosure_or_real`:
  a field algebraic over `ℚ` with a point on the quotient is isomorphic over `ℚ` either to
  `ℚ̄` or to the field of real algebraic numbers.
* `AlgebraicGeometry.RationalGaloisQuotient.universallyInjective_galoisQuotientToBase`:
  **Stacks 0483**, the structure morphism of the quotient is universally injective.

## Implementation notes

Taking spectra is contravariant, so a field automorphism is sent to the scheme
automorphism induced by its inverse.

The real algebraic numbers are the relative algebraic closure `algebraicClosure ℚ ℝ`.
Isomorphism of fields is expressed by a nonempty algebra equivalence, because the field of a
point of the quotient is not definitionally a chosen model of either field. A field-valued
point is evaluated at the object of the big fppf site given by a morphism from the field's
spectrum to `Spec ℚ`; that morphism is automatically the structure morphism, since `ℚ`
admits a unique ring homomorphism into a field.

Universal injectivity needs nothing of the algebraicity of the quotient: it is tested on
field-valued points, and the projection of `Spec ℚ̄` onto the quotient is locally surjective,
which lifts a section of the quotient over the spectrum of a field to a morphism to
`Spec ℚ̄` after one further field extension. Tag 0483 also asserts that this morphism is not
radicial; that half is not proved here, because stating it needs the quotient to be an
algebraic space and refuting it needs the classification of the field-valued points of the
quotient, neither of which is available in this library.

## References

* [Stacks Project, Tag 02Z6](https://stacks.math.columbia.edu/tag/02Z6)
* [Stacks Project, Tag 0483](https://stacks.math.columbia.edu/tag/0483)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- An endomorphism of the spectrum of a field inducing the canonical isomorphism of residue
fields at its unique point is the identity. -/
theorem Scheme.spec_hom_eq_id_of_residueFieldMap_eq_id {K : Type} [Field K]
    (f : Spec (.of K) ⟶ Spec (.of K))
    (hf : f.residueFieldMap (IsLocalRing.closedPoint K) =
      (Scheme.residueFieldCongr
        (Subsingleton.elim _ (IsLocalRing.closedPoint K))).hom) : f = 𝟙 _ := by
  apply (Scheme.SpecToEquivOfField K _).injective
  apply Scheme.SpecToEquivOfField_eq_iff.mpr
  refine ⟨Subsingleton.elim _ _, ?_⟩
  have hcomp := Scheme.descResidueField_stalkClosedPointTo_comp (f := f) (g := 𝟙 _)
  change _ = f.residueFieldMap (IsLocalRing.closedPoint K) ≫ _ at hcomp
  grind [Scheme.SpecToEquivOfField_apply_fst,
    Scheme.SpecToEquivOfField_apply_snd, CategoryTheory.id_apply]

/-- An endomorphism of the spectrum of a field which fixes a point and induces the canonical
isomorphism of residue fields there is the identity. -/
theorem Scheme.spec_hom_eq_id_of_residueFieldMap_eq_congr {K : Type} [Field K]
    (f : Spec (.of K) ⟶ Spec (.of K)) (x : Spec (.of K)) (hx : f x = x)
    (hf : f.residueFieldMap x = (Scheme.residueFieldCongr hx).hom) : f = 𝟙 _ := by
  obtain rfl : x = IsLocalRing.closedPoint K := Subsingleton.elim _ _
  exact Scheme.spec_hom_eq_id_of_residueFieldMap_eq_id f (by simpa using hf)

/-- A nonempty scheme locally of finite type over a field `K` receives a morphism from the
spectrum of a finite extension of `K`: a maximal ideal of the coordinate ring of an affine
open has residue field finite over `K` by Zariski's lemma. -/
private theorem exists_finiteDimensional_point {K : Type} [Field K] {X : Scheme.{0}}
    (p : X ⟶ Spec (.of K)) [LocallyOfFiniteType p] (x : X) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L),
      Nonempty (Spec (.of L) ⟶ X) := by
  classical
  obtain ⟨A, ι, hι, y, -⟩ := Scheme.exists_Spec_apply_eq x
  let : IsOpenImmersion ι := hι
  set φ : CommRingCat.of K ⟶ A := Spec.preimage (ι ≫ p)
  let : Algebra K A := φ.hom.toAlgebra
  have hmap : Spec.map φ = ι ≫ p := Spec.map_preimage _
  have hft : RingHom.FiniteType φ.hom :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp (hmap ▸ inferInstance)
  let : Algebra.FiniteType K A := hft
  obtain ⟨m, hm, -⟩ := y.asIdeal.exists_le_maximal y.isPrime.ne_top
  let : m.IsMaximal := hm
  let : Field (A ⧸ m) := Ideal.Quotient.field m
  let : Algebra.FiniteType K (A ⧸ m) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ K m) Ideal.Quotient.mk_surjective
  exact ⟨A ⧸ m, inferInstance, inferInstance, finite_of_finite_type_of_isJacobsonRing K (A ⧸ m),
    ⟨Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk m)) ≫ ι⟩⟩

namespace RationalGaloisQuotient

/-- The base `Spec ℚ`. -/
abbrev base : Scheme := Spec (.of ℚ)

/-- The spectrum of the algebraic closure of `ℚ`, as a scheme over `Spec ℚ`. -/
abbrev cover : Over base :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))))

variable (B : BigFppfSite.{0}) (hS : B.Contains base) (hU : B.Contains cover.left)

/-- The spectrum of the algebraic closure of `ℚ`, as an object of a big fppf site over
`Spec ℚ`. -/
def siteCover : BigFppfOver B base hS :=
  Over.mk (ObjectProperty.homMk cover.hom : B.obj hU ⟶ B.obj hS)

/-- The absolute Galois group of `ℚ`, as the group of algebra automorphisms of its algebraic
closure. -/
@[sga "3 VIIB 3.3.3" "special case"]
abbrev galoisGroup := AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ

/-- The action of the absolute Galois group of `ℚ` on `Spec ℚ̄` over `Spec ℚ`. Taking spectra
is contravariant, so an automorphism acts through its inverse. -/
def galoisAction : galoisGroup →* Aut (Space.underlyingOver B hS (siteCover B hS hU)) where
  toFun σ := .of <| Over.isoMk (Scheme.Spec.mapIso ((σ⁻¹).toRingEquiv.toCommRingCatIso).op)
    (specMapAlgAut_comp_structureMap ℚ (AlgebraicClosure ℚ) σ⁻¹)
  map_one' := Aut.ext <| Iso.ext <| Over.OverMorphism.ext <| specMapAlgAut_one ℚ (AlgebraicClosure ℚ)
  map_mul' σ τ := Aut.ext <| Iso.ext <| Over.OverMorphism.ext <|
    (congrArg (specMapAlgAut ℚ (AlgebraicClosure ℚ)) (mul_inv_rev σ τ)).trans
      (specMapAlgAut_mul ℚ (AlgebraicClosure ℚ) τ⁻¹ σ⁻¹)

/-- The fppf sheaf quotient `Spec ℚ̄ / Gal(ℚ̄/ℚ)`. -/
abbrev galoisQuotient [HasSheafify (BigFppfOver.topology B base hS) (Type 0)] :
    (BigFppfOver B base hS)ᵒᵖ ⥤ Type 0 :=
  Space.actionQuotient galoisGroup B hS (siteCover B hS hU) (galoisAction B hS hU)

/-- **Stacks 02Z6.** Every nonidentity element of the absolute Galois group of `ℚ` acts
nontrivially on the residue field at the unique point of `Spec ℚ̄`. -/
@[stacks 02Z6 "qbar_quotient_algebraic_space"]
theorem galoisAction_nontrivialOnFixedResidueFields :
    Space.ActsNontriviallyOnFixedResidueFields
      (Space.underlyingOver B hS (siteCover B hS hU)) galoisGroup (galoisAction B hS hU) := by
  intro g x hx hg h
  have hs : Spec.map (CommRingCat.ofHom (g⁻¹).toRingEquiv.toRingHom) =
      𝟙 (Spec (.of (AlgebraicClosure ℚ))) :=
    Scheme.spec_hom_eq_id_of_residueFieldMap_eq_congr _ x hx h
  apply hg ∘ inv_eq_one.mp
  ext z
  have hr := congrArg CommRingCat.Hom.hom (Spec.map_eq_id.mp hs)
  simpa using congrArg (fun φ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ => φ z) hr

/-- The part of **Stacks 02Z5** consumed here: a field-valued point of the Galois quotient
lifts to a morphism to `Spec ℚ̄` after a finite extension of the field.

A section of the quotient sheaf is, fppf-locally on the test object, the image of a morphism
to `Spec ℚ̄`; a covering sieve of `Spec K` has a member whose source is a nonempty `K`-scheme
locally of finite presentation, and a maximal ideal of an affine open of that source cuts out
a finite extension of `K`.

This is a private stand-in for tag 02Z5, stating only what is used below; delete it and use
the lift supplied by 02Z5 once that tag lands. -/
private theorem exists_finiteDimensional_hom_of_galoisQuotient_point
    (K : Type) [Field K] (hK : B.Contains (Spec (.of K))) (b : Spec (.of K) ⟶ base)
    (ξ : (galoisQuotient B hS hU).obj
      (op (Over.mk (ObjectProperty.homMk b : B.obj hK ⟶ B.obj hS)))) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L),
      Nonempty (AlgebraicClosure ℚ →+* L) := by
  let : Small.{0} galoisGroup := inferInstance
  set W : BigFppfOver B base hS :=
    Over.mk (ObjectProperty.homMk b : B.obj hK ⟶ B.obj hS)
  let J := BigFppfOver.topology B base hS
  let F : BigFppfOver B base hS ⥤ Over base := Over.post B.inclusion
  let j₀ := Space.actionRelation (Space.underlyingOver B hS (siteCover B hS hU))
    galoisGroup (galoisAction B hS hU)
  let : Presheaf.IsLocallySurjective J (Stacks.Groupoids.toQuotientSheaf J F j₀) :=
    Stacks.Groupoids.quotientPoint_locally_surjective J F j₀
  have hmem : Presheaf.imageSieve (Stacks.Groupoids.toQuotientSheaf J F j₀) ξ ∈ J W :=
    Presheaf.imageSieve_mem (U := op W) J (Stacks.Groupoids.toQuotientSheaf J F j₀) ξ
  obtain ⟨c, q, hq, -, hqlfp, hx⟩ :=
    BigFppfOver.exists_mem_of_mem_topology B base hS hmem
      (show (BigFppfOver.toScheme B base hS).obj W from IsLocalRing.closedPoint K)
  obtain ⟨g, -⟩ := hq
  let : LocallyOfFinitePresentation ((BigFppfOver.toScheme B base hS).map q) := hqlfp
  obtain ⟨x, -⟩ := hx
  obtain ⟨L, hLfield, hLalg, hLfin, ⟨ρ⟩⟩ :=
    exists_finiteDimensional_point ((BigFppfOver.toScheme B base hS).map q) x
  exact ⟨L, hLfield, hLalg, hLfin, ⟨(Spec.preimage (ρ ≫ g.left)).hom⟩⟩

/-- **Stacks 02Z6.** A field algebraic over `ℚ` carrying a point of the Galois quotient of
`Spec ℚ̄` is isomorphic over `ℚ` either to `ℚ̄` itself or to the field `algebraicClosure ℚ ℝ`
of real algebraic numbers.

The point lifts to a morphism `Spec L → Spec ℚ̄` for a finite extension `L` of the field, so
`L` is algebraic over `ℚ` and receives `ℚ̄`, hence is a copy of `ℚ̄` and is algebraically
closed; the Artin–Schreier degree bound in characteristic zero then leaves only degree one
and degree two, and the quadratic case is the real closure. -/
@[stacks 02Z6 "qbar_quotient_field_points"]
theorem fieldPoint_algEquiv_algebraicClosure_or_real
    (K : Type) [Field K] [Algebra ℚ K] [Algebra.IsAlgebraic ℚ K]
    (hK : B.Contains (Spec (.of K))) (b : Spec (.of K) ⟶ base)
    (ξ : (galoisQuotient B hS hU).obj
      (op (Over.mk (ObjectProperty.homMk b : B.obj hK ⟶ B.obj hS)))) :
    Nonempty (K ≃ₐ[ℚ] AlgebraicClosure ℚ) ∨
      Nonempty (K ≃ₐ[ℚ] algebraicClosure ℚ ℝ) := by
  obtain ⟨L, hLfield, hLalg, hLfin, ⟨j₀⟩⟩ :=
    exists_finiteDimensional_hom_of_galoisQuotient_point B hS hU K hK b ξ
  let : Field L := hLfield
  let : Algebra K L := hLalg
  let : FiniteDimensional K L := hLfin
  let : Algebra ℚ L := RingHom.toAlgebra ((algebraMap K L).comp (algebraMap ℚ K))
  have : IsScalarTower ℚ K L := .of_algebraMap_eq fun _ => rfl
  have : Algebra.IsAlgebraic ℚ L := Algebra.IsAlgebraic.trans ℚ K L
  let j : AlgebraicClosure ℚ →ₐ[ℚ] L := { j₀ with commutes' := j₀.map_rat_algebraMap }
  let eQ := algEquivOfAlgebraicClosureHom L j
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  have : IsAlgClosed L :=
    IsAlgClosed.of_ringEquiv (AlgebraicClosure ℚ) L eQ.symm.toRingEquiv
  rcases IsAlgClosed.finrank_eq_one_or_two K L with hd | hd
  · obtain ⟨e⟩ := Module.nonempty_algEquiv_iff_finrank_eq_one.mpr hd
    exact Or.inl ⟨(e.restrictScalars ℚ).trans eQ⟩
  · exact Or.inr (IsAlgClosed.nonempty_algEquiv_realAlgebraicClosure_of_finrank_two K L hd)

/-- `Spec ℚ̄` as a scheme over `Spec ℚ`, the object the Galois group acts on. -/
abbrev galoisCover : Over base :=
  Space.underlyingOver B hS (siteCover B hS hU)

/-- The graph relation of the Galois action on `Spec ℚ̄`. -/
abbrev galoisRelation :
    Stacks.Groupoids.PreRelation
      (Space.actionRelationScheme (galoisCover B hS hU) galoisGroup) (galoisCover B hS hU) :=
  Space.actionRelation (galoisCover B hS hU) galoisGroup (galoisAction B hS hU)

section UniversallyInjective

variable [HasSheafify (BigFppfOver.topology B base hS) (Type 0)]

/-- The projection of `Spec ℚ̄` onto its Galois quotient. -/
private noncomputable abbrev toGaloisQuotient :
    Stacks.Groupoids.points (Over.post (X := B.obj hS) B.inclusion) (galoisCover B hS hU) ⟶
      galoisQuotient B hS hU :=
  Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B base hS)
    (Over.post B.inclusion) (galoisRelation B hS hU)

/-- Two `T`-valued points of `Spec ℚ̄` in one orbit of the Galois action have the same image
in the Galois quotient. -/
private theorem toGaloisQuotient_app_eq_of_orbit (T : BigFppfOver B base hS)
    (f g : (Over.post (X := B.obj hS) B.inclusion).obj T ⟶ galoisCover B hS hU)
    (σ : galoisGroup) (hfg : g = f ≫ (galoisAction B hS hU σ).asIso.hom) :
    (toGaloisQuotient B hS hU).app (Opposite.op T) f =
      (toGaloisQuotient B hS hU).app (Opposite.op T) g := by
  have hsrcEq : (galoisRelation B hS hU).source =
      Space.actionRelationSource (galoisCover B hS hU) galoisGroup := by
    simp only [Space.actionRelation, prod.lift_snd]
  have htgtEq : (galoisRelation B hS hU).target =
      Space.actionRelationTarget (galoisCover B hS hU) galoisGroup (galoisAction B hS hU) := by
    simp only [Space.actionRelation, prod.lift_fst]
  have hs : (f ≫ Sigma.ι (fun _ : galoisGroup ↦ galoisCover B hS hU) σ) ≫
      (galoisRelation B hS hU).source = f := by
    rw [hsrcEq, Category.assoc, Space.actionRelationSource, Sigma.ι_desc, Category.comp_id]
  have ht : (f ≫ Sigma.ι (fun _ : galoisGroup ↦ galoisCover B hS hU) σ) ≫
      (galoisRelation B hS hU).target = g := by
    rw [htgtEq, Category.assoc, Space.actionRelationTarget, Sigma.ι_desc, hfg]
  have hrel := congrArg (fun η ↦ η (f ≫ Sigma.ι (fun _ : galoisGroup ↦ galoisCover B hS hU) σ))
    (NatTrans.congr_app (Stacks.Groupoids.sourceMap_toQuotientSheaf
      (BigFppfOver.topology B base hS) (Over.post B.inclusion) (galoisRelation B hS hU))
      (Opposite.op T))
  change (toGaloisQuotient B hS hU).app (Opposite.op T)
      ((f ≫ Sigma.ι (fun _ : galoisGroup ↦ galoisCover B hS hU) σ) ≫
        (galoisRelation B hS hU).source) =
    (toGaloisQuotient B hS hU).app (Opposite.op T)
      ((f ≫ Sigma.ι (fun _ : galoisGroup ↦ galoisCover B hS hU) σ) ≫
        (galoisRelation B hS hU).target) at hrel
  rw [hs, ht] at hrel
  exact hrel

/-- A morphism from the spectrum of a field to `Spec ℚ̄`, read as a `ℚ`-algebra map. -/
private noncomputable def algHomOfSpecMap (K : Type) [Field K] [Algebra ℚ K]
    (f : Spec (.of K) ⟶ Spec (.of (AlgebraicClosure ℚ))) : AlgebraicClosure ℚ →ₐ[ℚ] K :=
  (Spec.preimage f).hom.toRatAlgHom

/-- Taking spectra recovers the morphism a `ℚ`-algebra map was read off from. -/
private theorem specMap_algHomOfSpecMap (K : Type) [Field K] [Algebra ℚ K]
    (f : Spec (.of K) ⟶ Spec (.of (AlgebraicClosure ℚ))) :
    Spec.map (CommRingCat.ofHom (algHomOfSpecMap K f).toRingHom) = f := by
  simp [algHomOfSpecMap]

/-- Any two `ℚ`-embeddings of `ℚ̄` into a field differ by an element of the absolute Galois
group of `ℚ`, because `ℚ̄` is normal over `ℚ`. -/
private theorem exists_galoisGroup_comp (K : Type) [Field K] [Algebra ℚ K]
    (f g : AlgebraicClosure ℚ →ₐ[ℚ] K) :
    ∃ σ : galoisGroup, g = f.comp σ.toAlgHom := by
  let : Algebra (AlgebraicClosure ℚ) K := f.toRingHom.toAlgebra
  let : IsScalarTower ℚ (AlgebraicClosure ℚ) K :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (f.commutes x).symm
  let : Normal ℚ (AlgebraicClosure ℚ) :=
    { toIsAlgebraic := AlgebraicClosure.isAlgebraic ℚ
      splits' := fun x ↦ (AlgebraicClosure.isAlgClosed ℚ).splits
        ((minpoly ℚ x).map (algebraMap ℚ (AlgebraicClosure ℚ))) }
  let e := Normal.algHomEquivAut ℚ K (AlgebraicClosure ℚ)
  exact ⟨e g, (e.left_inv g).symm.trans (AlgHom.ext fun _ ↦ rfl)⟩

/-- The structure morphism of the Galois quotient of `Spec ℚ̄` to `Spec ℚ`, the unique
morphism to the presheaf represented by the base. -/
noncomputable def galoisQuotientToBase :
    galoisQuotient B hS hU ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hS))) := by
  let : PreservesLimit (Functor.empty.{0} (BigFppfOver B base hS)) yoneda := inferInstance
  exact ((Over.mkIdTerminal : IsTerminal (Over.mk (𝟙 (B.obj hS)))).isTerminalObj yoneda
    (Over.mk (𝟙 (B.obj hS)))).from _

/-- **Stacks 0483.** The Galois quotient of `Spec ℚ̄` is universally injective over `Spec ℚ`,
although it is not radicial.

Universal injectivity is tested on field-valued points, so it suffices to make two sections
of the quotient over the spectrum of a field agree over a further field spectrum. The
projection of `Spec ℚ̄` onto the quotient is locally surjective, so after two successive
restrictions both sections come from morphisms to `Spec ℚ̄`, that is from two `ℚ`-embeddings
of `ℚ̄` into the field of the second restriction; those differ by an element of the Galois
group, which is exactly what the quotient divides out. -/
@[stacks 0483 "universally injective"]
theorem universallyInjective_galoisQuotientToBase :
    Space.UniversallyInjective B base hS (galoisQuotientToBase B hS hU) := by
  refine Space.universallyInjective_of_fieldPoints B base hS _ ?_
  intro p y _
  have lift := Space.exists_fieldSpec_lift_of_isLocallySurjective B base hS
    (toGaloisQuotient B hS hU)
    (Stacks.Groupoids.toQuotientSheaf_isLocallySurjective (BigFppfOver.topology B base hS)
      (Over.post B.inclusion) (galoisRelation B hS hU))
  obtain ⟨L₁, hL₁f, hL₁, s₁, c₁, v₁, hv₁⟩ := lift p.carrier p.contained p.toBase p.value
  let : Field L₁ := hL₁f
  obtain ⟨L₂, hL₂f, hL₂, s₂, c₂, v₂, hv₂⟩ := lift L₁ hL₁ s₁ ((galoisQuotient B hS hU).map c₁.op y)
  let : Field L₂ := hL₂f
  set t₁ := (Stacks.Groupoids.points (Over.post (X := B.obj hS) B.inclusion)
    (galoisCover B hS hU)).map c₂.op v₁ with ht₁
  have hp : (galoisQuotient B hS hU).map (c₂ ≫ c₁).op p.value =
      (toGaloisQuotient B hS hU).app
        (Opposite.op (Over.mk (⟨s₂⟩ : B.obj hL₂ ⟶ B.obj hS))) t₁ := by
    rw [ht₁, NatTrans.naturality_apply (toGaloisQuotient B hS hU) c₂.op v₁, hv₁,
      op_comp, CategoryTheory.Functor.map_comp]
    rfl
  have hy : (galoisQuotient B hS hU).map (c₂ ≫ c₁).op y =
      (toGaloisQuotient B hS hU).app
        (Opposite.op (Over.mk (⟨s₂⟩ : B.obj hL₂ ⟶ B.obj hS))) v₂ := by
    rw [hv₂, op_comp, CategoryTheory.Functor.map_comp]
    rfl
  let : Algebra ℚ L₂ := (Spec.preimage s₂).hom.toAlgebra
  obtain ⟨σ, hσ⟩ := exists_galoisGroup_comp L₂ (algHomOfSpecMap L₂ t₁.left)
    (algHomOfSpecMap L₂ v₂.left)
  have hact : (galoisAction B hS hU σ⁻¹).asIso.hom.left =
      Spec.map (CommRingCat.ofHom σ.toRingEquiv.toRingHom) :=
    rfl
  have hcomp : Spec.map (CommRingCat.ofHom (algHomOfSpecMap L₂ v₂.left).toRingHom) =
      Spec.map (CommRingCat.ofHom (algHomOfSpecMap L₂ t₁.left).toRingHom) ≫
        Spec.map (CommRingCat.ofHom σ.toRingEquiv.toRingHom) := by
    rw [← Spec.map_comp]
    exact congrArg (fun φ : AlgebraicClosure ℚ →ₐ[ℚ] L₂ ↦ Spec.map (CommRingCat.ofHom φ.toRingHom))
      hσ
  have horbit : v₂ = t₁ ≫ (galoisAction B hS hU σ⁻¹).asIso.hom := by
    apply Over.OverMorphism.ext
    rw [Over.comp_left, hact, ← specMap_algHomOfSpecMap L₂ v₂.left,
      ← specMap_algHomOfSpecMap L₂ t₁.left]
    exact hcomp
  refine ⟨{ carrier := L₂
            field := hL₂f
            contained := hL₂
            toBase := s₂
            value := (galoisQuotient B hS hU).map (c₂ ≫ c₁).op p.value }, c₂ ≫ c₁, rfl, ?_⟩
  rw [hy, hp]
  exact (toGaloisQuotient_app_eq_of_orbit B hS hU (Over.mk (⟨s₂⟩ : B.obj hL₂ ⟶ B.obj hS))
    t₁ v₂ σ⁻¹ horbit).symm

end UniversallyInjective

end RationalGaloisQuotient

end AlgebraicGeometry

end
